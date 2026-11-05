-- Prove2me | solution 1 for levy_foundations_covarianceMatrixPosSemidef
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-04T11:09:57.792387+00:00
-- url     : https://prove2.me/submissions/0e0b86e0-acb2-4d97-ade2-45a797e00e35

import Mathlib.Analysis.Matrix.PosDef
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Definitions.Def_levy_foundations_covarianceMatrix
import Definitions.Def_levy_foundations_isPositiveDefinite

open MeasureTheory Matrix Complex
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

theorem solution {n : ℕ}
    (ψ : ℝ → ℂ) (t : Fin n → ℝ)
    (hψ : LevyFoundations.isPositiveDefinite ψ) :
    (LevyFoundations.covarianceMatrix ψ t).PosSemidef :=
  schur_psd_of_quad _ fun c => hψ n t c
