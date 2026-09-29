-- Prove2me | solution 1 for rademacher_l2_le_l1_of_l4_le_l2sq
-- status  : ACCEPTED   (prove)
-- author  : @Aphrodite
-- created : 2026-06-23T05:03:24.198817+00:00
-- url     : https://prove2.me/submissions/b0c589b3-b71d-43bf-9d15-ea2c93d84939

import Definitions.Def_matrix_completion_rademacher
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Sqrt
open MatrixCompletion
open scoped Classical BigOperators

/-
de la Peña–Montgomery-Smith 1995 (arXiv:math/9309211), Lemma 2 proof, the
L4 → L2 → L1 moment-transfer device, stated on the SYMMETRIC Rademacher (±1) fiber
`rademacherExpectation` (uniform `(1/2)^N` weights on sign assignments).

dlP–MS Lemma 2 (line "‖ξ‖₄ ≤ σ⁻ᵏ‖ξ‖₂ ⟹ ‖ξ‖₂ ≤ σ⁻²ᵏ‖ξ‖₁") transfers the
hypercontractive L4↔L2 control of the Rademacher chaos to an L2↔L1 control:
  ‖ξ‖₄ ≤ c‖ξ‖₂  ⟹  ‖ξ‖₂ ≤ c²‖ξ‖₁.
Squaring, on the uniform sign measure this is exactly
  E[F⁴] ≤ K·(E[F²])²  ⟹  E[F²] ≤ K·(E|F|)²,  K = c⁴.

Proof = two applications of Cauchy–Schwarz on the probability measure (uniform
weights `(1/2)^N`, nonneg + sum to 1 by the binomial theorem `(1/2 + 1/2)^N = 1`):
  (E F²)²  ≤ (E|F|)·(E|F|³)              [CS:  F² = √|F| · √|F|³]
  (E|F|³)² ≤ (E F²)·(E F⁴)              [CS:  |F|³ = √F² · √F⁴]
Combine with E F⁴ ≤ K(E F²)²:
  d² ≤ b·e ≤ K b³ ⇒ d ≤ √K b^{3/2};  b² ≤ a·d ≤ a√K b^{3/2} ⇒ b ≤ K a².

This is the Rademacher-fiber analogue of `bernoulli_l2_le_l1_of_l4_le_l2sq`
(b80931b4). The Rademacher form is MORE source-faithful: dlP–MS Lemma 2 and the
Bonami–Beckner inequality are naturally stated on the ±1 cube. No `p ∈ [0,1]`
hypothesis is needed: the uniform weights are unconditionally nonneg and sum to 1.
Cite dlP–MS 1995 Lemma 2 + Bonami 1970 / O'Donnell "Analysis of Boolean Functions"
Ch. 9 (hypercontractivity on the symmetric cube).
-/

theorem solution
    {n₁ n₂ : ℕ} (K : ℝ)
    (F : Finset (Fin n₁ × Fin n₂) → ℝ) :
    0 ≤ K →
    rademacherExpectation (fun ε => (F ε) ^ 4) ≤
        K * (rademacherExpectation (fun ε => (F ε) ^ 2)) ^ 2 →
    rademacherExpectation (fun ε => (F ε) ^ 2) ≤
        K * (rademacherExpectation (fun ε => |F ε|)) ^ 2 := by
  intro hK hHC
  classical
  -- weight nonnegativity
  have hw : ∀ ε : Finset (Fin n₁ × Fin n₂), 0 ≤ rademacherObservationWeight ε := by
    intro ε; unfold rademacherObservationWeight; positivity
  -- abbreviations for the four moments
  set a : ℝ := rademacherExpectation (fun ε => |F ε|) with ha
  set b : ℝ := rademacherExpectation (fun ε => (F ε) ^ 2) with hb
  set d : ℝ := rademacherExpectation (fun ε => |F ε| ^ 3) with hd
  set e : ℝ := rademacherExpectation (fun ε => (F ε) ^ 4) with he
  -- nonnegativity of the moments
  have hbnn : 0 ≤ b := by
    rw [hb]; unfold rademacherExpectation
    exact Finset.sum_nonneg (fun ε _ => mul_nonneg (hw ε) (by positivity))
  have hann : 0 ≤ a := by
    rw [ha]; unfold rademacherExpectation
    exact Finset.sum_nonneg (fun ε _ => mul_nonneg (hw ε) (abs_nonneg _))
  have hdnn : 0 ≤ d := by
    rw [hd]; unfold rademacherExpectation
    exact Finset.sum_nonneg (fun ε _ => mul_nonneg (hw ε) (by positivity))
  have henn : 0 ≤ e := by
    rw [he]; unfold rademacherExpectation
    exact Finset.sum_nonneg (fun ε _ => mul_nonneg (hw ε) (by positivity))
  -- CS step 1:  (E F²)² ≤ (E|F|)·(E|F|³)        via  (w·F²)² = (w·|F|)·(w·|F|³)
  have hCS1 : b ^ 2 ≤ a * d := by
    have hineq :
        (∑ ε : Finset (Fin n₁ × Fin n₂),
            rademacherObservationWeight ε * (F ε) ^ 2) ^ 2 ≤
          (∑ ε : Finset (Fin n₁ × Fin n₂),
              rademacherObservationWeight ε * |F ε|) *
            (∑ ε : Finset (Fin n₁ × Fin n₂),
              rademacherObservationWeight ε * |F ε| ^ 3) := by
      refine Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul Finset.univ
        (fun ε _ => mul_nonneg (hw ε) (abs_nonneg _))
        (fun ε _ => mul_nonneg (hw ε) (by positivity))
        (fun ε _ => ?_)
      have hF2 : (F ε) ^ 2 = |F ε| ^ 2 := (sq_abs (F ε)).symm
      rw [hF2]; ring
    rw [hb, ha, hd]
    simpa [rademacherExpectation] using hineq
  -- CS step 2:  (E|F|³)² ≤ (E F²)·(E F⁴)        via  (w·|F|³)² = (w·F²)·(w·F⁴)
  have hCS2 : d ^ 2 ≤ b * e := by
    have hineq :
        (∑ ε : Finset (Fin n₁ × Fin n₂),
            rademacherObservationWeight ε * |F ε| ^ 3) ^ 2 ≤
          (∑ ε : Finset (Fin n₁ × Fin n₂),
              rademacherObservationWeight ε * (F ε) ^ 2) *
            (∑ ε : Finset (Fin n₁ × Fin n₂),
              rademacherObservationWeight ε * (F ε) ^ 4) := by
      refine Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul Finset.univ
        (fun ε _ => mul_nonneg (hw ε) (by positivity))
        (fun ε _ => mul_nonneg (hw ε) (by positivity))
        (fun ε _ => ?_)
      have hF2 : (F ε) ^ 2 = |F ε| ^ 2 := (sq_abs (F ε)).symm
      have hF4 : (F ε) ^ 4 = |F ε| ^ 4 := by
        have : |F ε| ^ 4 = (|F ε| ^ 2) ^ 2 := by ring
        rw [this, sq_abs]; ring
      rw [hF2, hF4]; ring
    rw [hd, hb, he]
    simpa [rademacherExpectation] using hineq
  -- hypercontractivity hypothesis in the abbreviations:  e ≤ K·b²
  have hHC' : e ≤ K * b ^ 2 := by rw [he, hb]; exact hHC
  -- Algebra:  from d² ≤ b·e ≤ K b³  and  b² ≤ a·d,  conclude  b ≤ K a².
  have hd2 : d ^ 2 ≤ K * b ^ 3 := by
    calc d ^ 2 ≤ b * e := hCS2
      _ ≤ b * (K * b ^ 2) := by
            apply mul_le_mul_of_nonneg_left hHC' hbnn
      _ = K * b ^ 3 := by ring
  have hb4 : b ^ 4 ≤ a ^ 2 * (K * b ^ 3) := by
    calc b ^ 4 = (b ^ 2) ^ 2 := by ring
      _ ≤ (a * d) ^ 2 := by
            apply pow_le_pow_left₀ (by positivity) hCS1
      _ = a ^ 2 * d ^ 2 := by ring
      _ ≤ a ^ 2 * (K * b ^ 3) := by
            apply mul_le_mul_of_nonneg_left hd2 (by positivity)
  rcases eq_or_lt_of_le hbnn with hb0 | hbpos
  · rw [← hb0]; exact mul_nonneg hK (by positivity)
  · have hb3pos : 0 < b ^ 3 := by positivity
    have hrw : b ^ 4 = b * b ^ 3 := by ring
    have hrhs : a ^ 2 * (K * b ^ 3) = (K * a ^ 2) * b ^ 3 := by ring
    rw [hrw, hrhs] at hb4
    exact le_of_mul_le_mul_right hb4 hb3pos
