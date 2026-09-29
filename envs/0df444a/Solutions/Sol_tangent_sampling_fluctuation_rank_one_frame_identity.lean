-- Prove2me | solution 1 for tangent_sampling_fluctuation_rank_one_frame_identity
-- status  : ACCEPTED   (prove)
-- author  : @Hartmann_Psi
-- created : 2026-06-24T03:14:56.558423+00:00
-- url     : https://prove2.me/submissions/ec11ad63-60dc-4b26-9eb6-20448e1d6ead

import Definitions.Def_matrix_completion_tangent
open MatrixCompletion
open scoped BigOperators Matrix

set_option maxHeartbeats 1000000

/-
W2 — rank-one frame representation of the un-normalised tangent sampling
fluctuation (matrix form).

For a matrix `X` in the tangent space `T` (`tangentProjection S X = X`),

    P_T (P_Ω X) − p·X
      = ∑_{(a,b)} ((δ_{ab} − p) · X_{ab}) • P_T(e_a e_b^*)

where `δ_{ab} = [(a,b) ∈ Ω]` and `P_T(e_a e_b^*) = tangentProjection S
(coordinateMatrix a b)` =: `y_{ab}`.  Together with the HS-vectorization
isometry (clause C: `(vecMulVec (vec y_ab)(vec y_ab)).mulVec (vec H) =
⟨y_ab,H⟩_F • vec y_ab`, theorem `a3b0f6db`) and `X_{ab} = ⟨y_ab,X⟩_F` for X ∈ T,
this exhibits the fluctuation operator on T as the rank-one tensor sum
`∑ (δ_ab − p) y_ab ⊗ y_ab` whose operator norm is the deviation `Z`.  This is
the operator-sum representation that lets the general-{H_j} matrix NC-Khintchine
engine + bot6's Loewner collapse `d24a0b1f` be instantiated with
`H_ab = y_ab ⊗ y_ab` in the Rudelson selection lemma.

Source: Candès–Recht arXiv:0805.4471 §3–§4.2 (tangent sampling operator
`p^{-1}(P_T P_Ω P_T − p P_T)` as a sum of rank-one operators); Rudelson 1999
(J. Funct. Anal. 164, Thm 1, pp.3–6); van Handel "Structured Random Matrices" §3.

Proof: `P_Ω X = ∑_{ab} (δ_ab X_ab) e_ab` and (for X ∈ T) the resolution of
identity `X = ∑_{ab} X_ab y_ab` (= `P_T(∑ X_ab e_ab)`, by linearity of P_T over
the standard coordinate decomposition); apply `P_T` to the first using linearity
and homogeneity, then subtract `p·X`.  Elementary finite linear algebra over the
explicit SVD projection kernels; axiom-clean.
-/
theorem solution
    {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r)
    (Omega : Finset (Fin n1 × Fin n2)) (p : Real)
    (X : RealMatrix n1 n2) (hX : tangentProjection S X = X) :
    tangentProjection S (samplingProjection Omega X) - p • X
      = ∑ ab : Fin n1 × Fin n2,
          (((if ab ∈ Omega then (1:Real) else 0) - p) * X ab.1 ab.2)
            • tangentProjection S (coordinateMatrix ab.1 ab.2) := by
  -- ===== inlined infrastructure =====
  -- linearity of the three constituent projections over finite sums
  have left_sum : ∀ {ι : Type} (s : Finset ι) (f : ι → RealMatrix n1 n2),
      leftSingularProjection S (∑ t ∈ s, f t)
        = ∑ t ∈ s, leftSingularProjection S (f t) := by
    intro ι s f; funext i j
    rw [Matrix.sum_apply]
    unfold leftSingularProjection
    rw [show (∑ a, (∑ k, S.u k i * S.u k a) * (∑ t ∈ s, f t) a j)
          = ∑ a, ∑ t ∈ s, (∑ k, S.u k i * S.u k a) * f t a j by
          apply Finset.sum_congr rfl; intro a _
          rw [show ((∑ t ∈ s, f t) a j) = ∑ t ∈ s, f t a j by rw [Matrix.sum_apply]]
          rw [Finset.mul_sum]]
    rw [Finset.sum_comm]
  have right_sum : ∀ {ι : Type} (s : Finset ι) (f : ι → RealMatrix n1 n2),
      rightSingularProjection S (∑ t ∈ s, f t)
        = ∑ t ∈ s, rightSingularProjection S (f t) := by
    intro ι s f; funext i j
    rw [Matrix.sum_apply]
    unfold rightSingularProjection
    rw [show (∑ b, (∑ t ∈ s, f t) i b * (∑ l, S.v l b * S.v l j))
          = ∑ b, ∑ t ∈ s, f t i b * (∑ l, S.v l b * S.v l j) by
          apply Finset.sum_congr rfl; intro b _
          rw [show ((∑ t ∈ s, f t) i b) = ∑ t ∈ s, f t i b by rw [Matrix.sum_apply]]
          rw [Finset.sum_mul]]
    rw [Finset.sum_comm]
  have twoSided_sum : ∀ {ι : Type} (s : Finset ι) (f : ι → RealMatrix n1 n2),
      twoSidedSingularProjection S (∑ t ∈ s, f t)
        = ∑ t ∈ s, twoSidedSingularProjection S (f t) := by
    intro ι s f; funext i j
    rw [Matrix.sum_apply]
    unfold twoSidedSingularProjection
    rw [show (∑ a, ∑ b, (∑ k, S.u k i * S.u k a) * (∑ t ∈ s, f t) a b * (∑ l, S.v l b * S.v l j))
          = ∑ a, ∑ b, ∑ t ∈ s, (∑ k, S.u k i * S.u k a) * (f t a b) * (∑ l, S.v l b * S.v l j) by
          apply Finset.sum_congr rfl; intro a _
          apply Finset.sum_congr rfl; intro b _
          rw [show ((∑ t ∈ s, f t) a b) = ∑ t ∈ s, f t a b by rw [Matrix.sum_apply]]
          generalize (∑ k, S.u k i * S.u k a) = c
          generalize (∑ l, S.v l b * S.v l j) = d
          rw [Finset.mul_sum, Finset.sum_mul]]
    rw [show (∑ a, ∑ b, ∑ t ∈ s, (∑ k, S.u k i * S.u k a) * (f t a b) * (∑ l, S.v l b * S.v l j))
          = ∑ a, ∑ t ∈ s, ∑ b, (∑ k, S.u k i * S.u k a) * (f t a b) * (∑ l, S.v l b * S.v l j) by
          apply Finset.sum_congr rfl; intro a _
          rw [Finset.sum_comm]]
    rw [Finset.sum_comm]
  have tangent_sum : ∀ {ι : Type} (s : Finset ι) (f : ι → RealMatrix n1 n2),
      tangentProjection S (∑ t ∈ s, f t) = ∑ t ∈ s, tangentProjection S (f t) := by
    intro ι s f; unfold tangentProjection
    rw [left_sum, right_sum, twoSided_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  -- homogeneity of P_T
  have left_smul : ∀ (c : Real) (Y : RealMatrix n1 n2),
      leftSingularProjection S (c • Y) = c • leftSingularProjection S Y := by
    intro c Y; funext i j
    simp only [Matrix.smul_apply, smul_eq_mul]
    unfold leftSingularProjection
    simp only [Matrix.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro a _; ring
  have right_smul : ∀ (c : Real) (Y : RealMatrix n1 n2),
      rightSingularProjection S (c • Y) = c • rightSingularProjection S Y := by
    intro c Y; funext i j
    simp only [Matrix.smul_apply, smul_eq_mul]
    unfold rightSingularProjection
    simp only [Matrix.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro b _; ring
  have twoSided_smul : ∀ (c : Real) (Y : RealMatrix n1 n2),
      twoSidedSingularProjection S (c • Y) = c • twoSidedSingularProjection S Y := by
    intro c Y; funext i j
    simp only [Matrix.smul_apply, smul_eq_mul]
    unfold twoSidedSingularProjection
    simp only [Matrix.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro a _
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro b _; ring
  have tangent_smul : ∀ (c : Real) (Y : RealMatrix n1 n2),
      tangentProjection S (c • Y) = c • tangentProjection S Y := by
    intro c Y; unfold tangentProjection
    rw [left_smul, right_smul, twoSided_smul, smul_sub, smul_add]
  -- X = ∑_ab X_ab • coordinateMatrix a b
  have matrix_eq_sum_coord : X
      = ∑ ab : Fin n1 × Fin n2, X ab.1 ab.2 • coordinateMatrix ab.1 ab.2 := by
    funext i j
    rw [Matrix.sum_apply]
    simp only [coordinateMatrix, Matrix.smul_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_eq_single (i, j)]
    · simp
    · intro c _ hc
      rw [if_neg]; intro ⟨h1, h2⟩
      exact hc (by rw [Prod.ext_iff]; exact ⟨h1.symm, h2.symm⟩)
    · intro h; simp at h
  -- P_Ω X = ∑_ab (δ_ab * X_ab) • coordinateMatrix a b
  have sampling_eq_sum_coord : samplingProjection Omega X
      = ∑ ab : Fin n1 × Fin n2,
          ((if ab ∈ Omega then (1:Real) else 0) * X ab.1 ab.2)
            • coordinateMatrix ab.1 ab.2 := by
    funext i j; unfold samplingProjection
    rw [Matrix.sum_apply]
    simp only [coordinateMatrix, Matrix.smul_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_eq_single (i, j)]
    · by_cases h : (i,j) ∈ Omega <;> simp [h]
    · intro c _ hc
      rw [if_neg]; intro ⟨h1,h2⟩
      exact hc (by rw [Prod.ext_iff]; exact ⟨h1.symm, h2.symm⟩)
    · intro h; simp at h
  -- resolution of identity for X ∈ T
  have resolution : X = ∑ ab : Fin n1 × Fin n2,
      X ab.1 ab.2 • tangentProjection S (coordinateMatrix ab.1 ab.2) := by
    conv_lhs => rw [← hX, matrix_eq_sum_coord]
    rw [tangent_sum]
    apply Finset.sum_congr rfl; intro ab _; rw [tangent_smul]
  -- ===== assembly =====
  have hPTPO : tangentProjection S (samplingProjection Omega X)
      = ∑ ab : Fin n1 × Fin n2,
          ((if ab ∈ Omega then (1:Real) else 0) * X ab.1 ab.2)
            • tangentProjection S (coordinateMatrix ab.1 ab.2) := by
    rw [sampling_eq_sum_coord, tangent_sum]
    apply Finset.sum_congr rfl; intro ab _; rw [tangent_smul]
  have hpX : p • X = ∑ ab : Fin n1 × Fin n2,
      (p * X ab.1 ab.2) • tangentProjection S (coordinateMatrix ab.1 ab.2) := by
    conv_lhs => rw [resolution]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl; intro ab _; rw [smul_smul]
  rw [hPTPO, hpX, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro ab _
  rw [← sub_smul]; congr 1; ring
