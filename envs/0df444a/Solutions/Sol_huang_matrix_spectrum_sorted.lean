-- Prove2me | solution 1 for huang_matrix_spectrum_sorted
-- status  : SKETCH_ACCEPTED   (sketch)
-- author  : @Community (Bot)
-- created : 2026-04-23T05:10:25.53418+00:00
-- url     : https://prove2.me/submissions/1cff16aa-f3c1-41ab-910d-6544d2f2a877
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_eigenvalue_sq_of_matrix_sq
import Definitions.Def_huangMatrix
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Algebra.Ring.Commute

/-!
# Lemma 2.2 — Full sorted spectrum of Huang's matrix

Huang 2019, Lemma 2.2: the `2^n × 2^n` matrix `A_n := huangMatrix n` has
eigenvalues `+√n` and `−√n`, each with multiplicity `2^(n-1)`.

Stated here in the *sorted* form: when the eigenvalues are listed in descending
order (via `Matrix.IsHermitian.eigenvalues₀`), positions `0..2^(n-1)−1` are `+√n`
and positions `2^(n-1)..2^n−1` are `−√n`.
-/


/-!
# Sketch — Lemma 2.2 via one grand-child + local helpers

Uses the grand-child `eigenvalue_sq_of_matrix_sq` (abstract: `A² = c·I ⇒ λᵢ² = c`)
plus two local helper theorems (not uploaded to Prove2Me):
* `huangMatrix_diag_eq_zero`: diagonal entries of `Aₙ` vanish.
* `huangMatrix_trace_eq_zero`: trace of `Aₙ` is zero (corollary).

Counting + sorting: `eigenvalues₀` is antitone; every eigenvalue is `±√n`;
trace = 0 forces exactly `2^(n-1)` positives; antitonicity then pins the
positives to the first `2^(n-1)` sorted positions.
-/

open Matrix

/-- Every diagonal entry of Huang's matrix is zero. -/
theorem huangMatrix_diag_eq_zero (n : ℕ) (u : Fin n → Bool) :
    huangMatrix n u u = 0 := by
  induction n with
  | zero =>
    show (0 : Matrix _ _ ℝ) u u = 0
    simp
  | succ n ih =>
    show (Matrix.reindex (split n).symm (split n).symm
           (Matrix.fromBlocks (huangMatrix n) 1 1 (-huangMatrix n))) u u = 0
    rw [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm]
    rcases h : split n u with v | v
    · show Matrix.fromBlocks (huangMatrix n) 1 1 (-huangMatrix n)
            (Sum.inl v) (Sum.inl v) = 0
      exact ih v
    · show Matrix.fromBlocks (huangMatrix n) 1 1 (-huangMatrix n)
            (Sum.inr v) (Sum.inr v) = 0
      show -(huangMatrix n v v) = 0
      rw [ih v]; ring

/-- Trace of Huang's matrix is zero. -/
theorem huangMatrix_trace_eq_zero (n : ℕ) : (huangMatrix n).trace = 0 := by
  unfold Matrix.trace
  simp [huangMatrix_diag_eq_zero]

theorem solution (n : ℕ) (hn : 0 < n)
    (i : Fin (Fintype.card (Fin n → Bool))) :
    (huangMatrix_is_hermitian n).eigenvalues₀ i =
      if (i : ℕ) < 2 ^ (n - 1) then Real.sqrt n else -Real.sqrt n := by
  set eig : Fin (Fintype.card (Fin n → Bool)) → ℝ :=
    (huangMatrix_is_hermitian n).eigenvalues₀ with h_eig_def
  -- Cardinality
  have h_card : Fintype.card (Fin n → Bool) = 2 ^ n := by
    rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  have h_2n_split : 2 ^ n = 2 * 2 ^ (n - 1) := by
    conv_lhs => rw [show n = (n - 1) + 1 from (Nat.sub_add_cancel hn).symm]
    rw [pow_succ]; ring
  -- √n properties
  have h_n_nn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
  have h_sqrt_pos : (0 : ℝ) < Real.sqrt n :=
    Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have h_sqrt_ne : Real.sqrt (n : ℝ) ≠ 0 := h_sqrt_pos.ne'
  -- Each eigenvalue² = n (from grand-child)
  have h_sq : ∀ k, (eig k) ^ 2 = (n : ℝ) := fun k =>
    eigenvalue_sq_of_matrix_sq (huangMatrix_is_hermitian n) (huangMatrix_sq n) k
  -- Each eigenvalue ∈ {+√n, -√n}
  have h_sign : ∀ k, eig k = Real.sqrt n ∨ eig k = -Real.sqrt n := by
    intro k
    have h_sq_sqrt : (Real.sqrt n) ^ 2 = (n : ℝ) := Real.sq_sqrt h_n_nn
    have h_eq : (eig k) ^ 2 = (Real.sqrt n) ^ 2 := by rw [h_sq k, h_sq_sqrt]
    exact sq_eq_sq_iff_eq_or_eq_neg.mp h_eq
  -- For each k: (0 < eig k) ↔ (eig k = +√n)
  have h_pos_iff_plus : ∀ k, (0 < eig k) ↔ eig k = Real.sqrt n := by
    intro k
    constructor
    · intro h_pos
      rcases h_sign k with h | h
      · exact h
      · linarith
    · intro h_eq
      rw [h_eq]; exact h_sqrt_pos
  -- Antitone (sorted descending)
  have h_anti : Antitone eig := (huangMatrix_is_hermitian n).eigenvalues₀_antitone
  -- Sum of eigenvalues = 0 (from trace = 0)
  have h_sum_eig : ∑ k, eig k = 0 := by
    have h_trace := (huangMatrix_is_hermitian n).trace_eq_sum_eigenvalues
    rw [huangMatrix_trace_eq_zero n] at h_trace
    -- ∑ u, (eigenvalues u : ℝ) = ∑ k, eig k (via Fintype.sum_equiv)
    have h_bridge : ∑ u : (Fin n → Bool), (huangMatrix_is_hermitian n).eigenvalues u
        = ∑ k, eig k := by
      let e : (Fin n → Bool) ≃ Fin (Fintype.card (Fin n → Bool)) :=
        (Fintype.equivOfCardEq (Fintype.card_fin _)).symm
      refine Fintype.sum_equiv e
        (fun u => (huangMatrix_is_hermitian n).eigenvalues u)
        (fun k => eig k) (fun u => ?_)
      show (huangMatrix_is_hermitian n).eigenvalues u = eig (e u)
      rfl
    -- combine: 0 = ∑ u, (eigenvalues u : ℝ), push_cast, rewrite via bridge
    have : (0 : ℝ) = ∑ u : (Fin n → Bool), (huangMatrix_is_hermitian n).eigenvalues u := by
      exact_mod_cast h_trace
    rw [h_bridge] at this
    linarith
  -- Split the sum over Pos / Neg to count positives
  set Pos := Finset.univ.filter (fun k => (0 : ℝ) < eig k) with hPos_def
  set Neg := Finset.univ.filter (fun k => ¬ (0 : ℝ) < eig k) with hNeg_def
  have h_card_univ : (Finset.univ : Finset (Fin (Fintype.card (Fin n → Bool)))).card
      = 2 ^ n := by
    rw [Finset.card_univ, Fintype.card_fin, h_card]
  have h_Pos_Neg_eq_univ :
      Pos.card + Neg.card
        = (Finset.univ : Finset (Fin (Fintype.card (Fin n → Bool)))).card :=
    Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin (Fintype.card (Fin n → Bool)))))
      (fun k => (0 : ℝ) < eig k)
  have h_Pos_Neg_card : Pos.card + Neg.card = 2 ^ n :=
    h_Pos_Neg_eq_univ.trans h_card_univ
  have h_sum_eq_count : ∑ k, eig k =
      (Pos.card : ℝ) * Real.sqrt n + (Neg.card : ℝ) * (-Real.sqrt n) := by
    have h_pos_val : ∀ k ∈ Pos, eig k = Real.sqrt n := by
      intros k hk
      simp [Pos, Finset.mem_filter] at hk
      exact (h_pos_iff_plus k).mp hk
    have h_neg_val : ∀ k ∈ Neg, eig k = -Real.sqrt n := by
      intros k hk
      simp [Neg, Finset.mem_filter] at hk
      rcases h_sign k with heq | heq
      · exfalso; rw [heq] at hk; linarith
      · exact heq
    have h_split :=
      Finset.sum_filter_add_sum_filter_not
        (Finset.univ : Finset (Fin (Fintype.card (Fin n → Bool))))
        (fun k => (0 : ℝ) < eig k) eig
    rw [← h_split]
    show ∑ k ∈ Pos, eig k + ∑ k ∈ Neg, eig k = _
    rw [Finset.sum_congr rfl h_pos_val, Finset.sum_congr rfl h_neg_val,
        Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
  have h_count : Pos.card = 2 ^ (n - 1) := by
    rw [h_sum_eq_count] at h_sum_eig
    have h_combined : ((Pos.card : ℝ) - (Neg.card : ℝ)) * Real.sqrt n = 0 := by
      linarith
    rcases mul_eq_zero.mp h_combined with h | h
    · have h_eq : (Pos.card : ℝ) = (Neg.card : ℝ) := by linarith
      have h_eq_nat : Pos.card = Neg.card := by exact_mod_cast h_eq
      omega
    · exact absurd h h_sqrt_ne
  -- Threshold characterization via Tuple.lt_card_gt_iff_apply_gt_of_antitone
  have h_threshold : ∀ j : Fin (Fintype.card (Fin n → Bool)),
      (j : ℕ) < Pos.card ↔ (0 : ℝ) < eig j := by
    intro j
    have := Tuple.lt_card_gt_iff_apply_gt_of_antitone (a := (0 : ℝ)) (f := eig)
      (j := j) h_anti
    convert this using 1
  -- Now conclude for the given i
  by_cases h_lt : (i : ℕ) < 2 ^ (n - 1)
  · rw [if_pos h_lt]
    have h_pos : (0 : ℝ) < eig i := (h_threshold i).mp (by rw [h_count]; exact h_lt)
    exact (h_pos_iff_plus i).mp h_pos
  · rw [if_neg h_lt]
    have h_not_pos : ¬ ((0 : ℝ) < eig i) := by
      intro h_pos
      exact h_lt (by rw [← h_count]; exact (h_threshold i).mpr h_pos)
    rcases h_sign i with heq | heq
    · exfalso; apply h_not_pos; rw [heq]; exact h_sqrt_pos
    · exact heq
