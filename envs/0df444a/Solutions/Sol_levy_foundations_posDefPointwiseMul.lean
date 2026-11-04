-- Prove2me | solution 1 for levy_foundations_posDefPointwiseMul
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-03T23:03:22.111931+00:00
-- url     : https://prove2.me/submissions/4683afde-ba73-4f19-8226-b3a93f2ca389

import Mathlib.Analysis.Matrix.PosDef
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Definitions.Def_levy_foundations_isPositiveDefinite

open MeasureTheory Complex ComplexConjugate Finset Filter Topology Matrix
open scoped ComplexOrder

open Matrix in
theorem schur_cross {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) (t : ℂ) :
    star (Pi.single i (1:ℂ) + Pi.single j t) ⬝ᵥ (A *ᵥ (Pi.single i (1:ℂ) + Pi.single j t))
      = A i i + t * A i j + star t * A j i + star t * t * A j j := by
  simp [star_add, add_dotProduct, mulVec_add, dotProduct_add, mulVec_single,
    single_dotProduct]
  ring

open Matrix in
theorem schur_psd_of_quad {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (h : ∀ c : Fin n → ℂ, 0 ≤ ∑ i, ∑ j, starRingEnd ℂ (c i) * c j * A i j) : A.PosSemidef := by
  have hq : ∀ c : Fin n → ℂ, 0 ≤ star c ⬝ᵥ (A *ᵥ c) := by
    intro c
    have := h c
    convert this using 1
    simp only [dotProduct, mulVec, Pi.star_apply, Finset.mul_sum, RCLike.star_def]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ hq
  have hdiag : ∀ i, (A i i).im = 0 := fun i => by
    have := hq (Pi.single i (1:ℂ) + Pi.single i 0)
    rw [schur_cross] at this
    simpa using (Complex.nonneg_iff.mp this).2.symm
  ext i j
  rw [Matrix.conjTranspose_apply]
  have h1 := (Complex.nonneg_iff.mp (hq (Pi.single i (1:ℂ) + Pi.single j 1))).2.symm
  have h2 := (Complex.nonneg_iff.mp (hq (Pi.single i (1:ℂ) + Pi.single j Complex.I))).2.symm
  rw [schur_cross] at h1 h2
  have hi := hdiag i
  have hj := hdiag j
  simp [hi, hj] at h1 h2
  apply Complex.ext <;> simp <;> linarith

theorem schur_decomp {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ) (hB : B.PosSemidef) :
    ∃ (w : Fin n → Fin n → ℂ) (l : Fin n → ℝ), (∀ k, 0 ≤ l k) ∧
      ∀ i j, B i j = ∑ k, (l k : ℂ) * (starRingEnd ℂ (w k i) * w k j) := by
  refine ⟨fun k i => starRingEnd ℂ ((hB.1.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) i k),
    hB.1.eigenvalues, hB.eigenvalues_nonneg, fun i j => ?_⟩
  have h := hB.1.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at h
  conv_lhs => rw [h]
  simp [Matrix.mul_apply, Matrix.diagonal, Matrix.star_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem solution {φ ψ : ℝ → ℂ} (hφ : LevyFoundations.isPositiveDefinite φ)
    (hψ : LevyFoundations.isPositiveDefinite ψ) :
    LevyFoundations.isPositiveDefinite (fun x => φ x * ψ x) := by
  intro n x c
  have hB : (Matrix.of fun i j : Fin n => ψ (x i - x j)).PosSemidef :=
    schur_psd_of_quad _ fun c => hψ n x c
  obtain ⟨w, l, hl, hdec⟩ := schur_decomp _ hB
  have key : ∀ i j, starRingEnd ℂ (c i) * c j * (φ (x i - x j) * ψ (x i - x j)) =
      ∑ k, (l k : ℂ) * (starRingEnd ℂ (c i * w k i) * (c j * w k j) * φ (x i - x j)) := by
    intro i j
    have := hdec i j
    simp only [Matrix.of_apply] at this
    rw [this, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul]
    ring
  simp only [key]
  rw [Finset.sum_congr rfl fun i _ => Finset.sum_comm, Finset.sum_comm]
  refine Finset.sum_nonneg fun k _ => ?_
  simp only [← Finset.mul_sum]
  exact mul_nonneg (Complex.zero_le_real.mpr (hl k)) (hφ n x (fun i => c i * w k i))
