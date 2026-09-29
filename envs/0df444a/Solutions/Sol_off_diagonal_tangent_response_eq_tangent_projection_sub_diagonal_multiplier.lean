-- Prove2me | solution 1 for off_diagonal_tangent_response_eq_tangent_projection_sub_diagonal_multiplier
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-06-22T02:26:27.712895+00:00
-- url     : https://prove2.me/submissions/9eddec3b-a396-4ed7-8079-ca967f45a82d

import Definitions.Def_matrix_completion_neumann

open scoped Classical BigOperators

namespace MatrixCompletion

variable {n1 n2 r : Nat} {M : RealMatrix n1 n2}

/-- The kernel equals the (i,j) entry of P_T of the coordinate matrix. -/
lemma kernel_eq_entry (S : SVD M r) (a : Fin n1) (b : Fin n2) (i : Fin n1) (j : Fin n2) :
    tangentCoordinateKernel S a b i j
      = (tangentProjection S (coordinateMatrix a b)) i j := by
  unfold tangentCoordinateKernel matrixInner coordinateMatrix
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · simp
    · intro q _ hq; simp [hq]
    · intro h; exact absurd (Finset.mem_univ j) h
  · intro p _ hp
    apply Finset.sum_eq_zero
    intro q _
    rw [if_neg]
    · ring
    · rintro ⟨h1, _⟩; exact hp h1
  · intro h; exact absurd (Finset.mem_univ i) h

/-- Entry of P_T(e_w) at (i,j) in closed form. -/
lemma PT_coord_entry (S : SVD M r) (w1 : Fin n1) (w2 : Fin n2) (i : Fin n1) (j : Fin n2) :
    (tangentProjection S (coordinateMatrix w1 w2)) i j
      = (if j = w2 then (∑ k : Fin r, S.u k i * S.u k w1) else 0)
        + (if i = w1 then (∑ l : Fin r, S.v l w2 * S.v l j) else 0)
        - (∑ k : Fin r, S.u k i * S.u k w1) * (∑ l : Fin r, S.v l w2 * S.v l j) := by
  unfold tangentProjection
  simp only [Matrix.add_apply, Matrix.sub_apply, leftSingularProjection,
    rightSingularProjection, twoSidedSingularProjection, coordinateMatrix]
  congr 1
  · congr 1
    · rw [Finset.sum_eq_single w1]
      · by_cases hb : j = w2 <;> simp [hb]
      · intro aa _ haa; simp [haa]
      · intro h; exact absurd (Finset.mem_univ w1) h
    · rw [Finset.sum_eq_single w2]
      · by_cases ha : i = w1 <;> simp [ha]
      · intro bb _ hbb; simp [hbb]
      · intro h; exact absurd (Finset.mem_univ w2) h
  · rw [Finset.sum_eq_single w1]
    · rw [Finset.sum_eq_single w2]
      · simp
      · intro bb _ hbb; simp [hbb]
      · intro h; exact absurd (Finset.mem_univ w2) h
    · intro aa _ haa
      apply Finset.sum_eq_zero
      intro bb _
      rw [if_neg (by rintro ⟨h1,_⟩; exact haa h1)]; ring
    · intro h; exact absurd (Finset.mem_univ w1) h

/-- Direct entry of P_T X. -/
lemma PT_X_entry (S : SVD M r) (X : RealMatrix n1 n2) (i : Fin n1) (j : Fin n2) :
    (tangentProjection S X) i j
      = (∑ a : Fin n1, (∑ k : Fin r, S.u k i * S.u k a) * X a j)
        + (∑ b : Fin n2, X i b * (∑ l : Fin r, S.v l b * S.v l j))
        - (∑ a : Fin n1, ∑ b : Fin n2,
            (∑ k : Fin r, S.u k i * S.u k a) * X a b * (∑ l : Fin r, S.v l b * S.v l j)) := by
  unfold tangentProjection
  simp only [Matrix.add_apply, Matrix.sub_apply, leftSingularProjection,
    rightSingularProjection, twoSidedSingularProjection]

/-- Master expansion: entry of P_T X = sum over coordinates of X-entry times P_T(e_w) entry. -/
lemma PT_entry_eq_sum (S : SVD M r) (X : RealMatrix n1 n2) (i : Fin n1) (j : Fin n2) :
    (tangentProjection S X) i j
      = ∑ w : Fin n1 × Fin n2, X w.1 w.2 * (tangentProjection S (coordinateMatrix w.1 w.2)) i j := by
  rw [PT_X_entry]
  rw [Fintype.sum_prod_type]
  simp only [PT_coord_entry]
  rw [show (∑ x : Fin n1, ∑ y : Fin n2, X x y *
        ((if j = y then (∑ k : Fin r, S.u k i * S.u k x) else 0)
          + (if i = x then (∑ l : Fin r, S.v l y * S.v l j) else 0)
          - (∑ k : Fin r, S.u k i * S.u k x) * (∑ l : Fin r, S.v l y * S.v l j)))
      = (∑ x : Fin n1, ∑ y : Fin n2, X x y * (if j = y then (∑ k : Fin r, S.u k i * S.u k x) else 0))
        + (∑ x : Fin n1, ∑ y : Fin n2, X x y * (if i = x then (∑ l : Fin r, S.v l y * S.v l j) else 0))
        - (∑ x : Fin n1, ∑ y : Fin n2, X x y * ((∑ k : Fin r, S.u k i * S.u k x) * (∑ l : Fin r, S.v l y * S.v l j))) from by
    simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]]
  congr 1
  congr 1
  · rw [Finset.sum_comm]
    rw [Finset.sum_eq_single j]
    · apply Finset.sum_congr rfl; intro x _; simp; ring
    · intro y _ hy
      apply Finset.sum_eq_zero; intro x _; rw [if_neg (by exact fun h => hy h.symm)]; ring
    · intro h; exact absurd (Finset.mem_univ j) h
  · rw [Finset.sum_eq_single i]
    · apply Finset.sum_congr rfl; intro y _; simp
    · intro x _ hx
      apply Finset.sum_eq_zero; intro y _; rw [if_neg (by exact fun h => hx h.symm)]; ring
    · intro h; exact absurd (Finset.mem_univ i) h
  · apply Finset.sum_congr rfl; intro x _
    apply Finset.sum_congr rfl; intro y _; ring

/-- Sum-minus-single helper. -/
lemma sum_ite_zero_eq_sub (g : Fin n1 × Fin n2 → ℝ) (c : Fin n1 × Fin n2) :
    (∑ w, if w = c then (0:ℝ) else g w) = (∑ w, g w) - g c := by
  rw [eq_sub_iff_add_eq]
  rw [← Finset.sum_add_sum_compl {c}]
  rw [← Finset.sum_add_sum_compl {c} g]
  have h1 : (∑ w ∈ {c}, if w = c then (0:ℝ) else g w) = 0 := by simp
  have h2 : (∑ w ∈ ({c} : Finset (Fin n1 × Fin n2))ᶜ, if w = c then (0:ℝ) else g w)
      = ∑ w ∈ ({c}:Finset (Fin n1 × Fin n2))ᶜ, g w := by
    apply Finset.sum_congr rfl; intro w hw
    rw [if_neg]; intro h; subst h; simp at hw
  rw [h1, h2]
  simp
  ring

end MatrixCompletion

open MatrixCompletion

theorem solution
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (X : Matrix (Fin n₁) (Fin n₂) ℝ) :
    offDiagonalTangentResponse S X =
      tangentProjection S X - tangentDiagonalMultiplier S X := by
  funext i j
  show (∑ w : Fin n₁ × Fin n₂,
      if w = (i, j) then 0 else X w.1 w.2 * tangentCoordinateKernel S w.1 w.2 i j)
    = (tangentProjection S X) i j - tangentDiagonalMultiplier S X i j
  rw [PT_entry_eq_sum]
  simp only [← kernel_eq_entry]
  unfold tangentDiagonalMultiplier
  rw [sum_ite_zero_eq_sub (fun w => X w.1 w.2 * tangentCoordinateKernel S w.1 w.2 i j) (i, j)]
