-- Prove2me | solution 1 for tangent_sampling_concentration_implies_sampled_tangent_operator_frobenius_bound_pos
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-06-22T03:32:31.011104+00:00
-- url     : https://prove2.me/submissions/39306f4b-9e13-454b-b1b7-a3308dcb25c3

import Definitions.Def_matrix_completion_neumann
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt

open scoped Classical BigOperators
open MatrixCompletion

namespace MatrixCompletion

-- ===== inlined from Scratch_contraction.lean (Frobenius inner-product / projection library) =====
theorem tangentProjection_selfAdjoint {n1 n2 r : Nat} {M : RealMatrix n1 n2}
    (S : SVD M r) (X Y : RealMatrix n1 n2) :
    matrixInner X (tangentProjection S Y) = matrixInner (tangentProjection S X) Y := by
  unfold matrixInner tangentProjection
  simp only [Matrix.add_apply, Matrix.sub_apply]
  unfold leftSingularProjection rightSingularProjection twoSidedSingularProjection
  have h1 : (∑ i : Fin n1, ∑ j : Fin n2, X i j * (∑ a, (∑ k, S.u k i * S.u k a) * Y a j))
      = (∑ i : Fin n1, ∑ j : Fin n2, (∑ a, (∑ k, S.u k i * S.u k a) * X a j) * Y i j) := by
    have hLn : (∑ i : Fin n1, ∑ j : Fin n2, X i j * (∑ a, (∑ k, S.u k i * S.u k a) * Y a j))
        = ∑ i : Fin n1, ∑ a : Fin n1, ∑ j : Fin n2,
            (∑ k, S.u k i * S.u k a) * (X i j * Y a j) := by
      apply Finset.sum_congr rfl; intro i _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro a _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro j _; ring
    have hRn : (∑ i : Fin n1, ∑ j : Fin n2, (∑ a, (∑ k, S.u k i * S.u k a) * X a j) * Y i j)
        = ∑ i : Fin n1, ∑ a : Fin n1, ∑ j : Fin n2,
            (∑ k, S.u k i * S.u k a) * (X a j * Y i j) := by
      apply Finset.sum_congr rfl; intro i _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro a _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl; intro j _; ring
    rw [hLn, hRn, Finset.sum_comm]
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    have hk : (∑ k, S.u k a * S.u k i) = (∑ k, S.u k i * S.u k a) := by
      apply Finset.sum_congr rfl; intro k _; ring
    rw [hk]
  have h2 : (∑ i : Fin n1, ∑ j : Fin n2, X i j * (∑ b, Y i b * (∑ l, S.v l b * S.v l j)))
      = (∑ i : Fin n1, ∑ j : Fin n2, (∑ b, X i b * (∑ l, S.v l b * S.v l j)) * Y i j) := by
    apply Finset.sum_congr rfl; intro i _
    have hLn : (∑ j : Fin n2, X i j * (∑ b, Y i b * (∑ l, S.v l b * S.v l j)))
        = ∑ j : Fin n2, ∑ b : Fin n2, (∑ l, S.v l b * S.v l j) * (X i j * Y i b) := by
      apply Finset.sum_congr rfl; intro j _
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro b _; ring
    have hRn : (∑ j : Fin n2, (∑ b, X i b * (∑ l, S.v l b * S.v l j)) * Y i j)
        = ∑ j : Fin n2, ∑ b : Fin n2, (∑ l, S.v l b * S.v l j) * (X i b * Y i j) := by
      apply Finset.sum_congr rfl; intro j _
      rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro b _; ring
    rw [hLn, hRn, Finset.sum_comm]
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro b _
    have hk : (∑ l, S.v l j * S.v l b) = (∑ l, S.v l b * S.v l j) := by
      apply Finset.sum_congr rfl; intro l _; ring
    rw [hk]
  have h3 : (∑ i : Fin n1, ∑ j : Fin n2,
        X i j * (∑ a, ∑ b, (∑ k, S.u k i * S.u k a) * Y a b * (∑ l, S.v l b * S.v l j)))
      = (∑ i : Fin n1, ∑ j : Fin n2,
        (∑ a, ∑ b, (∑ k, S.u k i * S.u k a) * X a b * (∑ l, S.v l b * S.v l j)) * Y i j) := by
    have hLn : (∑ i : Fin n1, ∑ j : Fin n2,
          X i j * (∑ a, ∑ b, (∑ k, S.u k i * S.u k a) * Y a b * (∑ l, S.v l b * S.v l j)))
        = ∑ i : Fin n1, ∑ j : Fin n2, ∑ a : Fin n1, ∑ b : Fin n2,
            (∑ k, S.u k i * S.u k a) * (∑ l, S.v l b * S.v l j) * (X i j * Y a b) := by
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro a _
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro b _; ring
    have hRn : (∑ i : Fin n1, ∑ j : Fin n2,
          (∑ a, ∑ b, (∑ k, S.u k i * S.u k a) * X a b * (∑ l, S.v l b * S.v l j)) * Y i j)
        = ∑ i : Fin n1, ∑ j : Fin n2, ∑ a : Fin n1, ∑ b : Fin n2,
            (∑ k, S.u k i * S.u k a) * (∑ l, S.v l b * S.v l j) * (X a b * Y i j) := by
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _
      rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro a _
      rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro b _; ring
    rw [hLn, hRn]
    rw [show (∑ i : Fin n1, ∑ j : Fin n2, ∑ a : Fin n1, ∑ b : Fin n2,
          (∑ k, S.u k i * S.u k a) * (∑ l, S.v l b * S.v l j) * (X i j * Y a b))
        = ∑ q : (Fin n1 × Fin n2) × (Fin n1 × Fin n2),
            (∑ k, S.u k q.1.1 * S.u k q.2.1) * (∑ l, S.v l q.2.2 * S.v l q.1.2)
              * (X q.1.1 q.1.2 * Y q.2.1 q.2.2) from by
          simp_rw [Fintype.sum_prod_type]]
    rw [show (∑ i : Fin n1, ∑ j : Fin n2, ∑ a : Fin n1, ∑ b : Fin n2,
          (∑ k, S.u k i * S.u k a) * (∑ l, S.v l b * S.v l j) * (X a b * Y i j))
        = ∑ q : (Fin n1 × Fin n2) × (Fin n1 × Fin n2),
            (∑ k, S.u k q.1.1 * S.u k q.2.1) * (∑ l, S.v l q.2.2 * S.v l q.1.2)
              * (X q.2.1 q.2.2 * Y q.1.1 q.1.2) from by
          simp_rw [Fintype.sum_prod_type]]
    apply Finset.sum_nbij' (i := fun q => (q.2, q.1)) (j := fun q => (q.2, q.1))
    · intro p _; simp
    · intro p _; simp
    · intro p _; simp
    · intro p _; simp
    · intro p _
      have hku : (∑ k, S.u k p.2.1 * S.u k p.1.1) = (∑ k, S.u k p.1.1 * S.u k p.2.1) := by
        apply Finset.sum_congr rfl; intro k _; ring
      have hlv : (∑ l, S.v l p.1.2 * S.v l p.2.2) = (∑ l, S.v l p.2.2 * S.v l p.1.2) := by
        apply Finset.sum_congr rfl; intro l _; ring
      show _ = _
      simp only
      rw [hku, hlv]
  have hdistL : (∑ i : Fin n1, ∑ j : Fin n2,
        X i j * (((∑ a, (∑ k, S.u k i * S.u k a) * Y a j)
                  + (∑ b, Y i b * (∑ l, S.v l b * S.v l j))
                  - (∑ a, ∑ b, (∑ k, S.u k i * S.u k a) * Y a b * (∑ l, S.v l b * S.v l j)))))
      = (∑ i : Fin n1, ∑ j : Fin n2, X i j * (∑ a, (∑ k, S.u k i * S.u k a) * Y a j))
        + (∑ i : Fin n1, ∑ j : Fin n2, X i j * (∑ b, Y i b * (∑ l, S.v l b * S.v l j)))
        - (∑ i : Fin n1, ∑ j : Fin n2,
            X i j * (∑ a, ∑ b, (∑ k, S.u k i * S.u k a) * Y a b * (∑ l, S.v l b * S.v l j))) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro i _
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro j _; ring
  have hdistR : (∑ i : Fin n1, ∑ j : Fin n2,
        (((∑ a, (∑ k, S.u k i * S.u k a) * X a j)
                  + (∑ b, X i b * (∑ l, S.v l b * S.v l j))
                  - (∑ a, ∑ b, (∑ k, S.u k i * S.u k a) * X a b * (∑ l, S.v l b * S.v l j)))) * Y i j)
      = (∑ i : Fin n1, ∑ j : Fin n2, (∑ a, (∑ k, S.u k i * S.u k a) * X a j) * Y i j)
        + (∑ i : Fin n1, ∑ j : Fin n2, (∑ b, X i b * (∑ l, S.v l b * S.v l j)) * Y i j)
        - (∑ i : Fin n1, ∑ j : Fin n2,
            (∑ a, ∑ b, (∑ k, S.u k i * S.u k a) * X a b * (∑ l, S.v l b * S.v l j)) * Y i j) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro i _
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro j _; ring
  rw [hdistL, hdistR, h1, h2, h3]

-- ===== norm helpers =====

theorem matrixInner_self {n1 n2 : Nat} (X : RealMatrix n1 n2) :
    matrixInner X X = frobeniusNormSq X := by
  unfold matrixInner frobeniusNormSq
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  ring

theorem frobeniusNormSq_nonneg {n1 n2 : Nat} (X : RealMatrix n1 n2) :
    0 ≤ frobeniusNormSq X :=
  Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _))

theorem frobeniusNormSq_eq_sq {n1 n2 : Nat} (X : RealMatrix n1 n2) :
    frobeniusNormSq X = frobeniusNorm X ^ 2 := by
  unfold frobeniusNorm
  rw [Real.sq_sqrt (frobeniusNormSq_nonneg X)]

/-- Cauchy–Schwarz, squared form, for the Frobenius inner product. -/
theorem matrixInner_sq_le {n1 n2 : Nat} (X Y : RealMatrix n1 n2) :
    matrixInner X Y ^ 2 ≤ frobeniusNormSq X * frobeniusNormSq Y := by
  have hfold : (∑ i : Fin n1, ∑ j : Fin n2, X i j * Y i j)
        = ∑ q : Fin n1 × Fin n2, X q.1 q.2 * Y q.1 q.2 :=
    (Fintype.sum_prod_type (fun q => X q.1 q.2 * Y q.1 q.2)).symm
  have hfoldX : (∑ i : Fin n1, ∑ j : Fin n2, X i j ^ 2)
        = ∑ q : Fin n1 × Fin n2, X q.1 q.2 ^ 2 :=
    (Fintype.sum_prod_type (fun q => X q.1 q.2 ^ 2)).symm
  have hfoldY : (∑ i : Fin n1, ∑ j : Fin n2, Y i j ^ 2)
        = ∑ q : Fin n1 × Fin n2, Y q.1 q.2 ^ 2 :=
    (Fintype.sum_prod_type (fun q => Y q.1 q.2 ^ 2)).symm
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq
      (Finset.univ : Finset (Fin n1 × Fin n2))
      (fun q => X q.1 q.2) (fun q => Y q.1 q.2)
  unfold matrixInner frobeniusNormSq
  rw [hfold, hfoldX, hfoldY]
  exact hcs

-- ===== sampling-projection self-adjointness / idempotence (new, for this node) =====

theorem matrixInner_comm {n1 n2 : Nat} (X Y : RealMatrix n1 n2) :
    matrixInner X Y = matrixInner Y X := by
  unfold matrixInner
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _; ring

theorem sampling_selfAdjoint {n1 n2 : Nat} (Omega : Finset (Fin n1 × Fin n2))
    (X Y : RealMatrix n1 n2) :
    matrixInner X (samplingProjection Omega Y) = matrixInner (samplingProjection Omega X) Y := by
  unfold matrixInner samplingProjection
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  by_cases h : (i, j) ∈ Omega <;> simp [h]

theorem sampling_idem {n1 n2 : Nat} (Omega : Finset (Fin n1 × Fin n2))
    (X : RealMatrix n1 n2) :
    samplingProjection Omega (samplingProjection Omega X) = samplingProjection Omega X := by
  funext i j; unfold samplingProjection
  by_cases h : (i, j) ∈ Omega <;> simp [h]

theorem sampling_normSq_eq {n1 n2 : Nat} (Omega : Finset (Fin n1 × Fin n2))
    (X : RealMatrix n1 n2) :
    frobeniusNormSq (samplingProjection Omega X) = matrixInner X (samplingProjection Omega X) := by
  rw [← matrixInner_self]
  rw [matrixInner_comm (samplingProjection Omega X) (samplingProjection Omega X)]
  rw [← sampling_selfAdjoint Omega X (samplingProjection Omega X)]
  rw [sampling_idem]

end MatrixCompletion

/-- CORRECTED variant of c756305c with the omitted `0 < p` (and `0 ≤ epsilon`) hypotheses. -/
theorem solution
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (Omega : Finset (Fin n₁ × Fin n₂))
    (p epsilon : ℝ) :
    0 < p → 0 ≤ epsilon →
    epsilon ≤ (1 : ℝ) / 2 →
    TangentSamplingConcentration Omega S p epsilon →
    SampledTangentOperatorFrobeniusBound Omega S
      (Real.sqrt (((3 : ℝ) * p) / 2)) := by
  intro hp hε0 hε hTSC
  intro X hXT
  set A := samplingProjection Omega X with hA
  have hnormSq : frobeniusNormSq A = matrixInner X A := sampling_normSq_eq Omega X
  have hPT : matrixInner X A = matrixInner X (tangentProjection S A) := by
    have hsa := tangentProjection_selfAdjoint S X A
    rw [hsa, hXT]
  have hsplit : matrixInner X (tangentProjection S A)
      = matrixInner X (tangentProjection S A - p • X) + p * matrixInner X X := by
    unfold matrixInner
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i _
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro j _
    simp [Matrix.sub_apply, Matrix.smul_apply]; ring
  set D := tangentProjection S A - p • X with hD
  have hcs : matrixInner X D ^ 2 ≤ frobeniusNormSq X * frobeniusNormSq D := matrixInner_sq_le X D
  have hDbound : frobeniusNorm D ≤ epsilon * p * frobeniusNorm X := by
    have := hTSC X hXT
    simpa [hD, hA] using this
  have hXnn : 0 ≤ frobeniusNorm X := Real.sqrt_nonneg _
  have hDnn : 0 ≤ frobeniusNorm D := Real.sqrt_nonneg _
  have hcross : matrixInner X D ≤ frobeniusNorm X * (epsilon * p * frobeniusNorm X) := by
    have hle : matrixInner X D ≤ frobeniusNorm X * frobeniusNorm D := by
      have h1 : matrixInner X D ^ 2 ≤ (frobeniusNorm X * frobeniusNorm D) ^ 2 := by
        rw [mul_pow, ← frobeniusNormSq_eq_sq, ← frobeniusNormSq_eq_sq]; exact hcs
      nlinarith [le_abs_self (matrixInner X D), sq_abs (matrixInner X D),
        mul_nonneg hXnn hDnn, h1, abs_nonneg (matrixInner X D)]
    calc matrixInner X D ≤ frobeniusNorm X * frobeniusNorm D := hle
      _ ≤ frobeniusNorm X * (epsilon * p * frobeniusNorm X) :=
          mul_le_mul_of_nonneg_left hDbound hXnn
  have hXX : matrixInner X X = frobeniusNorm X ^ 2 := by
    rw [matrixInner_self, frobeniusNormSq_eq_sq]
  have hAsq_eq : frobeniusNorm A ^ 2 = matrixInner X D + p * matrixInner X X := by
    rw [← frobeniusNormSq_eq_sq, hnormSq, hPT, hsplit]
  have hAsq_le : frobeniusNorm A ^ 2 ≤ (3/2) * p * frobeniusNorm X ^ 2 := by
    rw [hAsq_eq, hXX]
    have hεp : epsilon * p ≤ (1/2) * p := mul_le_mul_of_nonneg_right hε (le_of_lt hp)
    nlinarith [hcross, hXnn, hp.le, sq_nonneg (frobeniusNorm X), hεp,
      mul_nonneg (le_of_lt hp) (sq_nonneg (frobeniusNorm X))]
  have hbound_nn : 0 ≤ Real.sqrt ((3 * p) / 2) := Real.sqrt_nonneg _
  have hAnn : 0 ≤ frobeniusNorm A := Real.sqrt_nonneg _
  have hsqrhs : (Real.sqrt ((3 * p) / 2) * frobeniusNorm X) ^ 2
      = (3/2) * p * frobeniusNorm X ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]; ring
  have hsq : frobeniusNorm A ^ 2 ≤ (Real.sqrt ((3 * p) / 2) * frobeniusNorm X) ^ 2 := by
    rw [hsqrhs]; exact hAsq_le
  nlinarith [hsq, hAnn, mul_nonneg hbound_nn hXnn,
    sq_nonneg (frobeniusNorm A - Real.sqrt ((3*p)/2) * frobeniusNorm X)]
