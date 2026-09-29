-- Prove2me | solution 1 for tangent_sampling_talagrand_variance_bound_from_coordinate_bound
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-06-21T04:32:46.468613+00:00
-- url     : https://prove2.me/submissions/7755e4c1-d1ce-4d0b-865b-75b7b7ecb3be

import Definitions.Def_matrix_completion_talagrand
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
open MatrixCompletion
open scoped Classical BigOperators

namespace MatrixCompletion

-- ===== bring in the proven pieces (copied) =====

theorem ker_idem {N r : Nat} (u : Fin r → (Fin N → ℝ))
    (horth : ∀ k l, ∑ i, u k i * u l i = if k = l then 1 else 0)
    (i b : Fin N) :
    (∑ a : Fin N, (∑ k : Fin r, u k i * u k a) * (∑ l : Fin r, u l a * u l b))
      = ∑ k : Fin r, u k i * u k b := by
  have e1 : (∑ a : Fin N, (∑ k : Fin r, u k i * u k a) * (∑ l : Fin r, u l a * u l b))
      = ∑ a : Fin N, ∑ k : Fin r, ∑ l : Fin r, (u k i * u k a) * (u l a * u l b) := by
    apply Finset.sum_congr rfl; intro a _; rw [Finset.sum_mul_sum]
  rw [e1, Finset.sum_comm]
  have e2 : (∑ k : Fin r, ∑ a : Fin N, ∑ l : Fin r, (u k i * u k a) * (u l a * u l b))
      = ∑ k : Fin r, ∑ l : Fin r, (u k i * u l b) * (∑ a : Fin N, u k a * u l a) := by
    apply Finset.sum_congr rfl; intro k _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro l _
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro a _; ring
  rw [e2]
  have e3 : (∑ k : Fin r, ∑ l : Fin r, (u k i * u l b) * (∑ a : Fin N, u k a * u l a))
      = ∑ k : Fin r, ∑ l : Fin r, (u k i * u l b) * (if k = l then 1 else 0) := by
    apply Finset.sum_congr rfl; intro k _; apply Finset.sum_congr rfl; intro l _; rw [horth k l]
  rw [e3]
  apply Finset.sum_congr rfl; intro k _
  have : (∑ l : Fin r, u k i * u l b * (if k = l then 1 else 0))
      = ∑ l : Fin r, (if k = l then u k i * u l b else 0) := by
    apply Finset.sum_congr rfl; intro l _; by_cases h : k = l <;> simp [h]
  rw [this, Finset.sum_ite_eq]; simp

theorem left_left {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r) (X : RealMatrix n1 n2) :
    leftSingularProjection S (leftSingularProjection S X) = leftSingularProjection S X := by
  funext i j
  unfold leftSingularProjection
  have : (∑ c : Fin n1, (∑ k : Fin r, S.u k i * S.u k c) *
            (∑ a : Fin n1, (∑ k : Fin r, S.u k c * S.u k a) * X a j))
      = ∑ a : Fin n1, (∑ k : Fin r, S.u k i * S.u k a) * X a j := by
    have hL : (∑ c : Fin n1, (∑ k : Fin r, S.u k i * S.u k c) *
            (∑ a : Fin n1, (∑ k : Fin r, S.u k c * S.u k a) * X a j))
        = ∑ a : Fin n1, (∑ c : Fin n1, (∑ k : Fin r, S.u k i * S.u k c) *
              (∑ k : Fin r, S.u k c * S.u k a)) * X a j := by
      have hLeft : (∑ c : Fin n1, (∑ k : Fin r, S.u k i * S.u k c) *
            (∑ a : Fin n1, (∑ k : Fin r, S.u k c * S.u k a) * X a j))
          = ∑ c : Fin n1, ∑ a : Fin n1,
              (∑ k : Fin r, S.u k i * S.u k c) * (∑ k : Fin r, S.u k c * S.u k a) * X a j := by
        apply Finset.sum_congr rfl; intro c _
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro a _; ring
      have hRight : (∑ a : Fin n1, (∑ c : Fin n1, (∑ k : Fin r, S.u k i * S.u k c) *
              (∑ k : Fin r, S.u k c * S.u k a)) * X a j)
          = ∑ a : Fin n1, ∑ c : Fin n1,
              (∑ k : Fin r, S.u k i * S.u k c) * (∑ k : Fin r, S.u k c * S.u k a) * X a j := by
        apply Finset.sum_congr rfl; intro a _
        rw [Finset.sum_mul]
      rw [hLeft, hRight, Finset.sum_comm]
    rw [hL]
    apply Finset.sum_congr rfl; intro a _
    rw [ker_idem S.u S.u_orthonormal i a]
  exact this

theorem right_right {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r) (X : RealMatrix n1 n2) :
    rightSingularProjection S (rightSingularProjection S X) = rightSingularProjection S X := by
  funext i j
  unfold rightSingularProjection
  have hR : (∑ b : Fin n2, (∑ c : Fin n2, X i c * (∑ l : Fin r, S.v l c * S.v l b)) *
              (∑ l : Fin r, S.v l b * S.v l j))
      = ∑ c : Fin n2, X i c * (∑ b : Fin n2,
            (∑ l : Fin r, S.v l c * S.v l b) * (∑ l : Fin r, S.v l b * S.v l j)) := by
    have hLeft : (∑ b : Fin n2, (∑ c : Fin n2, X i c * (∑ l : Fin r, S.v l c * S.v l b)) *
              (∑ l : Fin r, S.v l b * S.v l j))
        = ∑ b : Fin n2, ∑ c : Fin n2,
            X i c * ((∑ l : Fin r, S.v l c * S.v l b) * (∑ l : Fin r, S.v l b * S.v l j)) := by
      apply Finset.sum_congr rfl; intro b _
      rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro c _; ring
    have hRight : (∑ c : Fin n2, X i c * (∑ b : Fin n2,
            (∑ l : Fin r, S.v l c * S.v l b) * (∑ l : Fin r, S.v l b * S.v l j)))
        = ∑ c : Fin n2, ∑ b : Fin n2,
            X i c * ((∑ l : Fin r, S.v l c * S.v l b) * (∑ l : Fin r, S.v l b * S.v l j)) := by
      apply Finset.sum_congr rfl; intro c _
      rw [Finset.mul_sum]
    rw [hLeft, hRight, Finset.sum_comm]
  rw [hR]
  apply Finset.sum_congr rfl; intro c _
  rw [ker_idem S.v S.v_orthonormal c j]

theorem two_eq_left_right {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r)
    (X : RealMatrix n1 n2) :
    twoSidedSingularProjection S X = leftSingularProjection S (rightSingularProjection S X) := by
  funext i j
  unfold twoSidedSingularProjection leftSingularProjection rightSingularProjection
  apply Finset.sum_congr rfl; intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro b _; ring

theorem two_eq_right_left {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r)
    (X : RealMatrix n1 n2) :
    twoSidedSingularProjection S X = rightSingularProjection S (leftSingularProjection S X) := by
  funext i j
  unfold twoSidedSingularProjection leftSingularProjection rightSingularProjection
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro b _
  rw [Finset.sum_mul]

theorem left_add {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r) (A B : RealMatrix n1 n2) :
    leftSingularProjection S (A + B) = leftSingularProjection S A + leftSingularProjection S B := by
  funext i j
  simp only [Matrix.add_apply]
  unfold leftSingularProjection
  simp only [Matrix.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro a _; ring

theorem left_sub {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r) (A B : RealMatrix n1 n2) :
    leftSingularProjection S (A - B) = leftSingularProjection S A - leftSingularProjection S B := by
  funext i j
  simp only [Matrix.sub_apply]
  unfold leftSingularProjection
  simp only [Matrix.sub_apply]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro a _; ring

theorem right_add {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r) (A B : RealMatrix n1 n2) :
    rightSingularProjection S (A + B) = rightSingularProjection S A + rightSingularProjection S B := by
  funext i j
  simp only [Matrix.add_apply]
  unfold rightSingularProjection
  simp only [Matrix.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro b _; ring

theorem right_sub {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r) (A B : RealMatrix n1 n2) :
    rightSingularProjection S (A - B) = rightSingularProjection S A - rightSingularProjection S B := by
  funext i j
  simp only [Matrix.sub_apply]
  unfold rightSingularProjection
  simp only [Matrix.sub_apply]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro b _; ring

theorem left_two {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r) (X : RealMatrix n1 n2) :
    leftSingularProjection S (twoSidedSingularProjection S X) = twoSidedSingularProjection S X := by
  rw [two_eq_left_right S X, left_left S (rightSingularProjection S X)]

theorem right_two {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r) (X : RealMatrix n1 n2) :
    rightSingularProjection S (twoSidedSingularProjection S X) = twoSidedSingularProjection S X := by
  rw [two_eq_right_left S X, right_right S (leftSingularProjection S X)]

theorem left_tangent {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r) (X : RealMatrix n1 n2) :
    leftSingularProjection S (tangentProjection S X) = leftSingularProjection S X := by
  unfold tangentProjection
  rw [left_sub, left_add, left_left, ← two_eq_left_right, left_two]
  abel

theorem right_tangent {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r) (X : RealMatrix n1 n2) :
    rightSingularProjection S (tangentProjection S X) = rightSingularProjection S X := by
  unfold tangentProjection
  rw [right_sub, right_add, right_right, ← two_eq_right_left, right_two]
  abel

theorem two_tangent {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r) (X : RealMatrix n1 n2) :
    twoSidedSingularProjection S (tangentProjection S X) = twoSidedSingularProjection S X := by
  rw [two_eq_left_right S (tangentProjection S X), right_tangent, ← two_eq_left_right]

theorem tangent_idem {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r) (X : RealMatrix n1 n2) :
    tangentProjection S (tangentProjection S X) = tangentProjection S X := by
  conv_lhs => rw [tangentProjection]
  rw [left_tangent, right_tangent, two_tangent]
  rfl

-- ===== self-adjoint + coordinate (copied from Thm file) =====

theorem matrixInner_coordinateMatrix {n1 n2 : Nat} (X : RealMatrix n1 n2)
    (i : Fin n1) (j : Fin n2) :
    matrixInner X (coordinateMatrix i j) = X i j := by
  unfold matrixInner coordinateMatrix
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; simp at h
  · intro a _ ha
    apply Finset.sum_eq_zero
    intro b _; simp [ha]
  · intro h; simp at h

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

/-- The tangent projection is a Frobenius contraction. -/
theorem tangentProjection_contraction {n1 n2 r : Nat} {M : RealMatrix n1 n2}
    (S : SVD M r) (X : RealMatrix n1 n2) :
    frobeniusNormSq (tangentProjection S X) ≤ frobeniusNormSq X := by
  set Y := tangentProjection S X with hY
  -- ‖Y‖² = ⟨Y,Y⟩ = ⟨X, P_T(P_T X)⟩ = ⟨X, Y⟩
  have hself : matrixInner Y Y = matrixInner X Y := by
    -- selfAdjoint: ⟨X, P_T Y⟩ = ⟨P_T X, Y⟩.  With Y = P_T X, P_T Y = P_T(P_T X) = P_T X = Y.
    have hsa := tangentProjection_selfAdjoint S X Y
    rw [hY] at hsa
    rw [tangent_idem] at hsa
    -- hsa : matrixInner X (tangentProjection S X) = matrixInner (tangentProjection S X) (tangentProjection S X)
    rw [hY]
    exact hsa.symm
  have hYY : frobeniusNormSq Y = matrixInner X Y := by
    rw [← matrixInner_self Y, hself]
  -- ⟨X,Y⟩ ≤ ‖X‖‖Y‖ ; so ‖Y‖² ≤ ‖X‖‖Y‖
  have hcs : (matrixInner X Y) ^ 2 ≤ frobeniusNormSq X * frobeniusNormSq Y :=
    matrixInner_sq_le X Y
  have hYYnn : 0 ≤ frobeniusNormSq Y := frobeniusNormSq_nonneg Y
  have hXXnn : 0 ≤ frobeniusNormSq X := frobeniusNormSq_nonneg X
  -- from hYY: frobeniusNormSq Y = matrixInner X Y, so (frobeniusNormSq Y)^2 = (matrixInner X Y)^2 ≤ ‖X‖²‖Y‖²
  have hsq : (frobeniusNormSq Y) ^ 2 ≤ frobeniusNormSq X * frobeniusNormSq Y := by
    calc (frobeniusNormSq Y) ^ 2 = (matrixInner X Y) ^ 2 := by rw [hYY]
      _ ≤ frobeniusNormSq X * frobeniusNormSq Y := hcs
  -- conclude frobeniusNormSq Y ≤ frobeniusNormSq X
  rcases eq_or_lt_of_le hYYnn with h0 | hpos
  · rw [← h0]; exact hXXnn
  · -- divide hsq by frobeniusNormSq Y > 0
    have : frobeniusNormSq Y * frobeniusNormSq Y ≤ frobeniusNormSq X * frobeniusNormSq Y := by
      calc frobeniusNormSq Y * frobeniusNormSq Y = (frobeniusNormSq Y) ^ 2 := by ring
        _ ≤ frobeniusNormSq X * frobeniusNormSq Y := hsq
    exact le_of_mul_le_mul_right this hpos

/-- The Parseval contraction: ∑ ⟨X, P_T e_ij⟩² ≤ ‖X‖²_F. -/
theorem tangent_projection_coordinate_parseval_contraction
    {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r) (X : RealMatrix n1 n2) :
    (∑ i : Fin n1, ∑ j : Fin n2,
      matrixInner X (tangentProjection S (coordinateMatrix i j)) ^ 2)
      ≤ frobeniusNormSq X := by
  -- rewrite each term: ⟨X, P_T e_ij⟩ = ⟨P_T X, e_ij⟩ = (P_T X) i j
  have hterm : ∀ i : Fin n1, ∀ j : Fin n2,
      matrixInner X (tangentProjection S (coordinateMatrix i j))
        = tangentProjection S X i j := by
    intro i j
    rw [tangentProjection_selfAdjoint S X (coordinateMatrix i j)]
    rw [matrixInner_coordinateMatrix]
  have hrw : (∑ i : Fin n1, ∑ j : Fin n2,
      matrixInner X (tangentProjection S (coordinateMatrix i j)) ^ 2)
      = ∑ i : Fin n1, ∑ j : Fin n2, tangentProjection S X i j ^ 2 := by
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    rw [hterm i j]
  rw [hrw]
  -- this is frobeniusNormSq (P_T X)
  have heq : (∑ i : Fin n1, ∑ j : Fin n2, tangentProjection S X i j ^ 2)
      = frobeniusNormSq (tangentProjection S X) := rfl
  rw [heq]
  exact tangentProjection_contraction S X

end MatrixCompletion

open MatrixCompletion
open scoped Classical BigOperators

theorem solution :
    ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
      (μ₀ : ℝ) (S : SVD M r),
      0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
      1 ≤ μ₀ →
      TangentCoordinateFrobeniusBound S
        (2 * μ₀ * (r : ℝ) / (max n₁ n₂ : ℝ)) →
      TangentSamplingTalagrandVarianceBound S
        ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
        (2 * μ₀ * (↑(max n₁ n₂)) * (r : ℝ) / (m : ℝ)) := by
  intro n₁ n₂ r m M μ₀ S hn1 hn2 hr hm hμ₀ hcoord
  intro X1 X2 hX1 hX2
  set p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)) with hp
  have hn1R : (0 : ℝ) < n₁ := by exact_mod_cast hn1
  have hn2R : (0 : ℝ) < n₂ := by exact_mod_cast hn2
  have hmaxN : 0 < max n₁ n₂ := lt_of_lt_of_le hn1 (le_max_left _ _)
  have hmaxR : (0 : ℝ) < (max n₁ n₂ : ℝ) := by exact_mod_cast hmaxN
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · -- m = 0: p = 0, each term has p*(1-p)*coeff² but coeff has p⁻¹ = 0... actually
    -- coeff = p⁻¹*... = 0 when p=0; and p*(1-p) = 0. The whole sum is 0 ≤ σ²(=0... but ≥0 needed).
    subst hm0
    have hp0 : p = 0 := by rw [hp]; simp
    show (∑ i : Fin n₁, ∑ j : Fin n₂,
        p * (1 - p) * (tangentSamplingTalagrandCoefficient S p X1 X2 i j) ^ 2)
        ≤ 2 * μ₀ * (↑(max n₁ n₂)) * (r : ℝ) / ((0:ℕ):ℝ)
    rw [hp0]
    simp
  have hmR : (0 : ℝ) < m := by exact_mod_cast hmpos
  have hppos : 0 < p := by rw [hp]; positivity
  have hpinvpos : 0 < p⁻¹ := inv_pos.mpr hppos
  have hp1 : 1 - p ≤ 1 := by
    have : 0 ≤ p := hppos.le; linarith
  -- The variance bound goal
  show (∑ i : Fin n₁, ∑ j : Fin n₂,
      p * (1 - p) * (tangentSamplingTalagrandCoefficient S p X1 X2 i j) ^ 2)
      ≤ 2 * μ₀ * (↑(max n₁ n₂)) * (r : ℝ) / (m : ℝ)
  -- Per-term bound: p(1-p)coeff² ≤ p⁻¹·(2μ₀r/max)·⟨X1,Pe⟩²
  set R : ℝ := 2 * μ₀ * (r : ℝ) / (max n₁ n₂ : ℝ) with hR
  have hRnn : 0 ≤ R := by rw [hR]; positivity
  have hμ₀nn : 0 ≤ μ₀ := by linarith
  have hX1sq : frobeniusNormSq X1 ≤ 1 := by
    have := hX1
    rw [frobeniusNormSq_eq_sq]
    have h0 : 0 ≤ frobeniusNorm X1 := Real.sqrt_nonneg _
    nlinarith [this, h0]
  have hterm : ∀ i : Fin n₁, ∀ j : Fin n₂,
      p * (1 - p) * (tangentSamplingTalagrandCoefficient S p X1 X2 i j) ^ 2
        ≤ p⁻¹ * R *
          (matrixInner X1 (tangentProjection S (coordinateMatrix i j)) ^ 2) := by
    intro i j
    set Pe := tangentProjection S (coordinateMatrix i j) with hPe
    have hPesq : frobeniusNorm Pe ^ 2 ≤ R := hcoord i j
    have hPesqF : frobeniusNormSq Pe ≤ R := by rw [frobeniusNormSq_eq_sq]; exact hPesq
    -- coeff = p⁻¹ * ⟨X1,Pe⟩ * ⟨Pe,X2⟩
    unfold tangentSamplingTalagrandCoefficient
    rw [← hPe]
    set a : ℝ := matrixInner X1 Pe with ha
    set b : ℝ := matrixInner Pe X2 with hb
    -- (p⁻¹ * a * b)^2 = p⁻² a² b²
    have hexp : (p⁻¹ * a * b) ^ 2 = (p⁻¹)^2 * a ^ 2 * b ^ 2 := by ring
    rw [hexp]
    -- p(1-p) * (p⁻² a² b²) = (1-p) p⁻¹ a² b²
    have hpne : p ≠ 0 := ne_of_gt hppos
    have hcollapse : p * (1 - p) * ((p⁻¹)^2 * a ^ 2 * b ^ 2)
        = (1 - p) * p⁻¹ * a ^ 2 * b ^ 2 := by
      rw [inv_pow]
      field_simp
    rw [hcollapse]
    -- b² ≤ ‖Pe‖² * ‖X2‖² ≤ R
    have hb2 : b ^ 2 ≤ R := by
      have hcs : b ^ 2 ≤ frobeniusNormSq Pe * frobeniusNormSq X2 := MatrixCompletion.matrixInner_sq_le Pe X2
      have hX2sq : frobeniusNormSq X2 ≤ 1 := by
        rw [frobeniusNormSq_eq_sq]
        have h0 : 0 ≤ frobeniusNorm X2 := Real.sqrt_nonneg _
        nlinarith [hX2, h0]
      have hPeF0 : 0 ≤ frobeniusNormSq Pe :=
        Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _))
      calc b ^ 2 ≤ frobeniusNormSq Pe * frobeniusNormSq X2 := hcs
        _ ≤ frobeniusNormSq Pe * 1 := by
            apply mul_le_mul_of_nonneg_left hX2sq hPeF0
        _ = frobeniusNormSq Pe := by ring
        _ ≤ R := hPesqF
    -- (1-p)p⁻¹ ≤ p⁻¹
    have h1p : (1 - p) * p⁻¹ ≤ p⁻¹ := by
      have : (1 - p) ≤ 1 := by linarith
      calc (1 - p) * p⁻¹ ≤ 1 * p⁻¹ := mul_le_mul_of_nonneg_right this hpinvpos.le
        _ = p⁻¹ := by ring
    -- assemble: (1-p)p⁻¹ a² b² ≤ p⁻¹ a² R = p⁻¹ R a²
    have ha2nn : 0 ≤ a ^ 2 := sq_nonneg _
    have hb2nn : 0 ≤ b ^ 2 := sq_nonneg _
    calc (1 - p) * p⁻¹ * a ^ 2 * b ^ 2
          ≤ p⁻¹ * a ^ 2 * b ^ 2 := by
            apply mul_le_mul_of_nonneg_right _ hb2nn
            apply mul_le_mul_of_nonneg_right h1p ha2nn
      _ ≤ p⁻¹ * a ^ 2 * R := by
            apply mul_le_mul_of_nonneg_left hb2
            positivity
      _ = p⁻¹ * R * a ^ 2 := by ring
  -- Sum the per-term bound
  have hsum1 : (∑ i : Fin n₁, ∑ j : Fin n₂,
      p * (1 - p) * (tangentSamplingTalagrandCoefficient S p X1 X2 i j) ^ 2)
      ≤ ∑ i : Fin n₁, ∑ j : Fin n₂,
          p⁻¹ * R * (matrixInner X1 (tangentProjection S (coordinateMatrix i j)) ^ 2) := by
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    exact hterm i j
  -- Pull out the constant p⁻¹ * R and apply Parseval contraction
  have hpull : (∑ i : Fin n₁, ∑ j : Fin n₂,
      p⁻¹ * R * (matrixInner X1 (tangentProjection S (coordinateMatrix i j)) ^ 2))
      = p⁻¹ * R * (∑ i : Fin n₁, ∑ j : Fin n₂,
          matrixInner X1 (tangentProjection S (coordinateMatrix i j)) ^ 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
  have hpars := tangent_projection_coordinate_parseval_contraction S X1
  -- p⁻¹ R * (∑ ...) ≤ p⁻¹ R * ‖X1‖² ≤ p⁻¹ R * 1 = p⁻¹ R ≤ σ²
  have hprRnn : 0 ≤ p⁻¹ * R := mul_nonneg hpinvpos.le hRnn
  have hstep : p⁻¹ * R * (∑ i : Fin n₁, ∑ j : Fin n₂,
          matrixInner X1 (tangentProjection S (coordinateMatrix i j)) ^ 2)
      ≤ p⁻¹ * R := by
    calc p⁻¹ * R * (∑ i : Fin n₁, ∑ j : Fin n₂,
              matrixInner X1 (tangentProjection S (coordinateMatrix i j)) ^ 2)
          ≤ p⁻¹ * R * frobeniusNormSq X1 :=
            mul_le_mul_of_nonneg_left hpars hprRnn
      _ ≤ p⁻¹ * R * 1 := mul_le_mul_of_nonneg_left hX1sq hprRnn
      _ = p⁻¹ * R := by ring
  -- final arithmetic: p⁻¹ * R ≤ σ²  (same as increment final step)
  have hfinal : p⁻¹ * R ≤ 2 * μ₀ * (↑(max n₁ n₂)) * (r : ℝ) / (m : ℝ) := by
    have hpinv : p⁻¹ = ((n₁ : ℝ) * (n₂ : ℝ)) / (m : ℝ) := by rw [hp]; rw [inv_div]
    rw [hpinv, hR]
    have hprod : (n₁ : ℝ) * (n₂ : ℝ) ≤ (max n₁ n₂ : ℝ) * (max n₁ n₂ : ℝ) := by
      have h1 : (n₁ : ℝ) ≤ (max n₁ n₂ : ℝ) := by exact_mod_cast le_max_left n₁ n₂
      have h2 : (n₂ : ℝ) ≤ (max n₁ n₂ : ℝ) := by exact_mod_cast le_max_right n₁ n₂
      calc (n₁ : ℝ) * (n₂ : ℝ) ≤ (max n₁ n₂ : ℝ) * (n₂ : ℝ) :=
            mul_le_mul_of_nonneg_right h1 hn2R.le
        _ ≤ (max n₁ n₂ : ℝ) * (max n₁ n₂ : ℝ) :=
            mul_le_mul_of_nonneg_left h2 hmaxR.le
    rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hmR]
    rw [mul_div_assoc', div_le_iff₀ hmaxR]
    have hc : (0 : ℝ) ≤ 2 * μ₀ * (r : ℝ) := by positivity
    have hcast : (↑(max n₁ n₂) : ℝ) = max (n₁ : ℝ) (n₂ : ℝ) := by push_cast; ring
    rw [hcast]
    calc (n₁ : ℝ) * (n₂ : ℝ) * (2 * μ₀ * (r : ℝ))
          ≤ (max (n₁:ℝ) (n₂:ℝ) * max (n₁:ℝ) (n₂:ℝ)) * (2 * μ₀ * (r : ℝ)) :=
            mul_le_mul_of_nonneg_right hprod hc
      _ = 2 * μ₀ * max (n₁:ℝ) (n₂:ℝ) * ↑r * max (n₁:ℝ) (n₂:ℝ) := by ring
  calc (∑ i : Fin n₁, ∑ j : Fin n₂,
        p * (1 - p) * (tangentSamplingTalagrandCoefficient S p X1 X2 i j) ^ 2)
        ≤ ∑ i : Fin n₁, ∑ j : Fin n₂,
            p⁻¹ * R * (matrixInner X1 (tangentProjection S (coordinateMatrix i j)) ^ 2) := hsum1
    _ = p⁻¹ * R * (∑ i : Fin n₁, ∑ j : Fin n₂,
          matrixInner X1 (tangentProjection S (coordinateMatrix i j)) ^ 2) := hpull
    _ ≤ p⁻¹ * R := hstep
    _ ≤ 2 * μ₀ * (↑(max n₁ n₂)) * (r : ℝ) / (m : ℝ) := hfinal
