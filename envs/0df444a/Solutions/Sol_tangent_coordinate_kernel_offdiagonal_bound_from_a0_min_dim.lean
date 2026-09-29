-- Prove2me | solution 1 for tangent_coordinate_kernel_offdiagonal_bound_from_a0_min_dim
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-06-23T05:50:15.89966+00:00
-- url     : https://prove2.me/submissions/e6cda329-7049-43de-952b-3da179d9fdae

import Definitions.Def_matrix_completion_neumann
import Theorems.Thm_tangent_coordinate_kernel_diagonal_bound_from_a0_min_dim

open MatrixCompletion
open scoped BigOperators

namespace MatrixCompletion

/-! ## matrixInner linearity helpers -/

theorem matrixInner_comm {n1 n2 : Nat} (X Y : RealMatrix n1 n2) :
    matrixInner X Y = matrixInner Y X := by
  unfold matrixInner
  refine Finset.sum_congr rfl (fun i _ => ?_)
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

theorem matrixInner_add_right {n1 n2 : Nat} (X Y Z : RealMatrix n1 n2) :
    matrixInner X (Y + Z) = matrixInner X Y + matrixInner X Z := by
  unfold matrixInner
  simp only [Matrix.add_apply, mul_add]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.sum_add_distrib]

theorem matrixInner_sub_right {n1 n2 : Nat} (X Y Z : RealMatrix n1 n2) :
    matrixInner X (Y - Z) = matrixInner X Y - matrixInner X Z := by
  unfold matrixInner
  simp only [Matrix.sub_apply, mul_sub]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.sum_sub_distrib]

theorem matrixInner_zero_right {n1 n2 : Nat} (X : RealMatrix n1 n2) :
    matrixInner X 0 = 0 := by
  unfold matrixInner
  simp

/-! ## Generic kernel self-adjointness

Every projection `P` here has the form `(P X) i j = ∑ a, ∑ b, K i j a b * X a b`
for a kernel `K` with the symmetry `K i j a b = K a b i j`.  Such a `P` is
self-adjoint for `matrixInner`. -/

-- Swap the outer index pair (i,j) with the inner index pair (a,b) in a 4-fold sum.
private theorem sum_pair_collapse {n1 n2 : Nat}
    (G : Fin n1 → Fin n2 → Real) :
    (∑ i, ∑ j, G i j)
      = ∑ p : Fin n1 × Fin n2, G p.1 p.2 := by
  rw [← Finset.sum_product']
  rfl

private theorem sum4_swap {n1 n2 : Nat}
    (F : Fin n1 → Fin n2 → Fin n1 → Fin n2 → Real) :
    (∑ i, ∑ j, ∑ a, ∑ b, F i j a b) = (∑ a, ∑ b, ∑ i, ∑ j, F i j a b) := by
  have h1 : (∑ i, ∑ j, ∑ a, ∑ b, F i j a b)
      = ∑ p : Fin n1 × Fin n2, ∑ q : Fin n1 × Fin n2, F p.1 p.2 q.1 q.2 := by
    rw [sum_pair_collapse (fun i j => ∑ a, ∑ b, F i j a b)]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [sum_pair_collapse (fun a b => F p.1 p.2 a b)]
  have h2 : (∑ a, ∑ b, ∑ i, ∑ j, F i j a b)
      = ∑ q : Fin n1 × Fin n2, ∑ p : Fin n1 × Fin n2, F p.1 p.2 q.1 q.2 := by
    rw [sum_pair_collapse (fun a b => ∑ i, ∑ j, F i j a b)]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [sum_pair_collapse (fun i j => F i j q.1 q.2)]
  rw [h1, h2, Finset.sum_comm]

theorem matrixInner_kernel_selfAdjoint {n1 n2 : Nat}
    (K : Fin n1 → Fin n2 → Fin n1 → Fin n2 → Real)
    (hK : ∀ i j a b, K i j a b = K a b i j)
    (X Y : RealMatrix n1 n2) :
    matrixInner (fun i j => ∑ a, ∑ b, K i j a b * X a b) Y
      = matrixInner X (fun i j => ∑ a, ∑ b, K i j a b * Y a b) := by
  unfold matrixInner
  simp only [Finset.sum_mul, Finset.mul_sum]
  -- LHS: ∑ i ∑ j ∑ a ∑ b, K i j a b * X a b * Y i j
  -- RHS: ∑ i ∑ j ∑ a ∑ b, X i j * (K i j a b * Y a b)
  -- Swap (i,j)<->(a,b) on the RHS, then match termwise via hK.
  rw [sum4_swap (fun i j a b => X i j * (K i j a b * Y a b))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  refine Finset.sum_congr rfl (fun j _ => ?_)
  refine Finset.sum_congr rfl (fun a _ => ?_)
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [hK a b i j]
  ring

/-! ## Self-adjointness of each projection, via the generic kernel lemma -/

theorem leftSingularProjection_selfAdjoint {n1 n2 r : Nat} {M : RealMatrix n1 n2}
    (S : SVD M r) (X Y : RealMatrix n1 n2) :
    matrixInner (leftSingularProjection S X) Y = matrixInner X (leftSingularProjection S Y) := by
  have hL : ∀ (Z : RealMatrix n1 n2),
      leftSingularProjection S Z
        = (fun i j => ∑ a, ∑ b, ((∑ k, S.u k i * S.u k a) * (if b = j then 1 else 0)) * Z a b) := by
    intro Z
    funext i j
    unfold leftSingularProjection
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; exact absurd (Finset.mem_univ j) h
  rw [hL X, hL Y]
  refine matrixInner_kernel_selfAdjoint _ ?_ X Y
  intro i j a b
  by_cases hbj : b = j <;> by_cases hji : j = b
  · subst hbj; simp; refine Finset.sum_congr rfl (fun k _ => ?_); ring
  · subst hbj; exact absurd rfl hji
  · exact absurd hji.symm hbj
  · simp [hbj, fun h : j = b => hji h]

theorem rightSingularProjection_selfAdjoint {n1 n2 r : Nat} {M : RealMatrix n1 n2}
    (S : SVD M r) (X Y : RealMatrix n1 n2) :
    matrixInner (rightSingularProjection S X) Y = matrixInner X (rightSingularProjection S Y) := by
  have hR : ∀ (Z : RealMatrix n1 n2),
      rightSingularProjection S Z
        = (fun i j => ∑ a, ∑ b, ((if a = i then 1 else 0) * (∑ k, S.v k b * S.v k j)) * Z a b) := by
    intro Z
    funext i j
    unfold rightSingularProjection
    -- LHS: ∑ b, Z i b * d b j ;  RHS: ∑ a ∑ b ((if a=i then 1 else 0)*d b j)*Z a b
    symm
    rw [Finset.sum_eq_single i]
    · refine Finset.sum_congr rfl (fun b _ => ?_); simp; ring
    · intro a _ ha; refine Finset.sum_eq_zero (fun b _ => ?_); simp [ha]
    · intro h; exact absurd (Finset.mem_univ i) h
  rw [hR X, hR Y]
  refine matrixInner_kernel_selfAdjoint _ ?_ X Y
  intro i j a b
  by_cases hai : a = i <;> by_cases hia : i = a
  · subst hai; simp; refine Finset.sum_congr rfl (fun k _ => ?_); ring
  · subst hai; exact absurd rfl hia
  · exact absurd hia.symm hai
  · simp [hai, fun h : i = a => hia h]

theorem twoSidedSingularProjection_selfAdjoint {n1 n2 r : Nat} {M : RealMatrix n1 n2}
    (S : SVD M r) (X Y : RealMatrix n1 n2) :
    matrixInner (twoSidedSingularProjection S X) Y
      = matrixInner X (twoSidedSingularProjection S Y) := by
  have hT : ∀ (Z : RealMatrix n1 n2),
      twoSidedSingularProjection S Z
        = (fun i j => ∑ a, ∑ b,
            ((∑ k, S.u k i * S.u k a) * (∑ l, S.v l b * S.v l j)) * Z a b) := by
    intro Z
    funext i j
    unfold twoSidedSingularProjection
    refine Finset.sum_congr rfl (fun a _ => ?_)
    refine Finset.sum_congr rfl (fun b _ => ?_)
    ring
  rw [hT X, hT Y]
  refine matrixInner_kernel_selfAdjoint _ ?_ X Y
  intro i j a b
  -- K i j a b = (∑k u k i u k a)(∑l v l b v l j); K a b i j = (∑k u k a u k i)(∑l v l j v l i)... careful
  -- Actually K a b i j = (∑k u k a u k i)(∑l v l j v l b)
  have hu : (∑ k, S.u k i * S.u k a) = (∑ k, S.u k a * S.u k i) := by
    refine Finset.sum_congr rfl (fun k _ => ?_); ring
  have hv : (∑ l, S.v l b * S.v l j) = (∑ l, S.v l j * S.v l b) := by
    refine Finset.sum_congr rfl (fun l _ => ?_); ring
  rw [hu, hv]

/-! ## Projector idempotency from orthonormality

`Pu i a = ∑ k, u k i * u k a` is the column-space projector; it is idempotent:
`∑ a', Pu i a' * Pu a' a = Pu i a`.  Same for `Pv`. -/

-- ∑ c ∑ k ∑ l F c k l = ∑ k ∑ l ∑ c F c k l (move first index innermost).
private theorem sum3_rot {γ κ μ : Type*} [Fintype γ] [Fintype κ] [Fintype μ]
    (F : γ → κ → μ → Real) :
    (∑ c, ∑ k, ∑ l, F c k l) = ∑ k, ∑ l, ∑ c, F c k l := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Finset.sum_comm]

private theorem u_proj_idem {n1 r : Nat} (u : Fin r → (Fin n1 → Real))
    (hu : ∀ k l, ∑ i, u k i * u l i = if k = l then 1 else 0) (i a : Fin n1) :
    (∑ c, (∑ k, u k i * u k c) * (∑ l, u l c * u l a)) = ∑ k, u k i * u k a := by
  have hflat : (∑ c, (∑ k, u k i * u k c) * (∑ l, u l c * u l a))
      = ∑ c, ∑ k, ∑ l, (u k i * u l a) * (u k c * u l c) := by
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    ring
  rw [hflat, sum3_rot (fun c k l => (u k i * u l a) * (u k c * u l c))]
  have hstep : (∑ k, ∑ l, ∑ c, (u k i * u l a) * (u k c * u l c))
      = ∑ k, ∑ l, (u k i * u l a) * (∑ c, u k c * u l c) := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [Finset.mul_sum]
  rw [hstep]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Finset.sum_eq_single k]
  · rw [hu k k]; simp
  · intro l _ hl; rw [hu k l]; simp [Ne.symm hl]
  · intro h; exact absurd (Finset.mem_univ k) h

private theorem v_proj_idem {n2 r : Nat} (v : Fin r → (Fin n2 → Real))
    (hv : ∀ k l, ∑ j, v k j * v l j = if k = l then 1 else 0) (b j : Fin n2) :
    (∑ c, (∑ k, v k b * v k c) * (∑ l, v l c * v l j)) = ∑ k, v k b * v k j := by
  have hflat : (∑ c, (∑ k, v k b * v k c) * (∑ l, v l c * v l j))
      = ∑ c, ∑ k, ∑ l, (v k b * v l j) * (v k c * v l c) := by
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    ring
  rw [hflat, sum3_rot (fun c k l => (v k b * v l j) * (v k c * v l c))]
  have hstep : (∑ k, ∑ l, ∑ c, (v k b * v l j) * (v k c * v l c))
      = ∑ k, ∑ l, (v k b * v l j) * (∑ c, v k c * v l c) := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [Finset.mul_sum]
  rw [hstep]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Finset.sum_eq_single k]
  · rw [hv k k]; simp
  · intro l _ hl; rw [hv k l]; simp [Ne.symm hl]
  · intro h; exact absurd (Finset.mem_univ k) h

/-! ## Composition relations of the three projections -/

-- L ∘ L = L
private theorem LL {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r) (X : RealMatrix n1 n2) :
    leftSingularProjection S (leftSingularProjection S X) = leftSingularProjection S X := by
  funext i j
  unfold leftSingularProjection
  -- ∑ a, Pu i a * (∑ a', Pu a a' * X a' j) = ∑ a', Pu i a' * X a' j
  have hflat : (∑ a, (∑ k, S.u k i * S.u k a) * ∑ a', (∑ k, S.u k a * S.u k a') * X a' j)
      = ∑ a, ∑ a', (∑ k, S.u k i * S.u k a) * ((∑ k, S.u k a * S.u k a') * X a' j) := by
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.mul_sum]
  have h1 : (∑ a, (∑ k, S.u k i * S.u k a) * ∑ a', (∑ k, S.u k a * S.u k a') * X a' j)
      = ∑ a', (∑ c, (∑ k, S.u k i * S.u k c) * (∑ l, S.u l c * S.u l a')) * X a' j := by
    rw [hflat, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun a' _ => ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    ring
  rw [h1]
  refine Finset.sum_congr rfl (fun a' _ => ?_)
  rw [u_proj_idem S.u S.u_orthonormal i a']

-- R ∘ R = R
private theorem RR {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r) (X : RealMatrix n1 n2) :
    rightSingularProjection S (rightSingularProjection S X) = rightSingularProjection S X := by
  funext i j
  unfold rightSingularProjection
  have hflat : (∑ b, (∑ b', X i b' * ∑ k, S.v k b' * S.v k b) * ∑ k, S.v k b * S.v k j)
      = ∑ b, ∑ b', (X i b' * (∑ k, S.v k b' * S.v k b)) * (∑ k, S.v k b * S.v k j) := by
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [Finset.sum_mul]
  have h1 : (∑ b, (∑ b', X i b' * ∑ k, S.v k b' * S.v k b) * ∑ k, S.v k b * S.v k j)
      = ∑ b', X i b' * (∑ c, (∑ k, S.v k b' * S.v k c) * (∑ l, S.v l c * S.v l j)) := by
    rw [hflat, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun b' _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    ring
  rw [h1]
  refine Finset.sum_congr rfl (fun b' _ => ?_)
  rw [v_proj_idem S.v S.v_orthonormal b' j]

-- L ∘ R = T2  (apply L to (R X))
private theorem LR {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r) (X : RealMatrix n1 n2) :
    leftSingularProjection S (rightSingularProjection S X)
      = twoSidedSingularProjection S X := by
  funext i j
  unfold leftSingularProjection rightSingularProjection twoSidedSingularProjection
  -- ∑ a, Pu i a * (∑ b, X a b * Pv b j) = ∑ a ∑ b, Pu i a * X a b * Pv b j
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  ring

-- R ∘ L = T2
private theorem RL {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r) (X : RealMatrix n1 n2) :
    rightSingularProjection S (leftSingularProjection S X)
      = twoSidedSingularProjection S X := by
  funext i j
  unfold rightSingularProjection leftSingularProjection twoSidedSingularProjection
  -- ∑ b, (∑ a, Pu i a * X a b) * Pv b j = ∑ a ∑ b, Pu i a * X a b * Pv b j
  have hflat : (∑ b, (∑ a, (∑ k, S.u k i * S.u k a) * X a b) * ∑ k, S.v k b * S.v k j)
      = ∑ b, ∑ a, ((∑ k, S.u k i * S.u k a) * X a b) * (∑ k, S.v k b * S.v k j) := by
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [Finset.sum_mul]
  rw [hflat, Finset.sum_comm]

-- T2 = R ∘ L, so by associativity of these compositions we derive the rest.
-- L ∘ T2 = T2 : L (T2 X) = L (L (R X)) = L (R X) = T2 X   (uses LL and LR)
private theorem LT2 {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r) (X : RealMatrix n1 n2) :
    leftSingularProjection S (twoSidedSingularProjection S X)
      = twoSidedSingularProjection S X := by
  rw [← LR S X, LL S (rightSingularProjection S X)]

-- T2 ∘ L = T2 : T2 (L X).  T2 = R∘L composition? Actually twoSided applied to (L X).
-- Use T2 X = R (L X) (RL), and T2 (L X) = R (L (L X)) = R (L X) = T2 X.
private theorem T2L {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r) (X : RealMatrix n1 n2) :
    twoSidedSingularProjection S (leftSingularProjection S X)
      = twoSidedSingularProjection S X := by
  rw [← RL S (leftSingularProjection S X), LL S X, RL S X]

-- R ∘ T2 = T2 : R (T2 X) = R (R (L X)) = R (L X) = T2 X  (uses RL and RR)
private theorem RT2 {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r) (X : RealMatrix n1 n2) :
    rightSingularProjection S (twoSidedSingularProjection S X)
      = twoSidedSingularProjection S X := by
  rw [← RL S X, RR S (leftSingularProjection S X)]

-- T2 ∘ R = T2 : T2 (R X) = R (L (R X)) = R (T2 X)... use LR then RT2.
private theorem T2R {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r) (X : RealMatrix n1 n2) :
    twoSidedSingularProjection S (rightSingularProjection S X)
      = twoSidedSingularProjection S X := by
  rw [← RL S (rightSingularProjection S X), LR S X, RT2 S X]

-- T2 ∘ T2 = T2 : T2 (T2 X) = R (L (T2 X)) = R (T2 X) = T2 X.
private theorem T2T2 {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r) (X : RealMatrix n1 n2) :
    twoSidedSingularProjection S (twoSidedSingularProjection S X)
      = twoSidedSingularProjection S X := by
  rw [← RL S (twoSidedSingularProjection S X), LT2 S X, RT2 S X]

/-! ## Linearity of the projections (additive over +, -) -/

private theorem left_add {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r)
    (A B : RealMatrix n1 n2) :
    leftSingularProjection S (A + B)
      = leftSingularProjection S A + leftSingularProjection S B := by
  funext i j
  simp only [Matrix.add_apply]
  unfold leftSingularProjection
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  simp only [Matrix.add_apply]; ring

private theorem left_sub {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r)
    (A B : RealMatrix n1 n2) :
    leftSingularProjection S (A - B)
      = leftSingularProjection S A - leftSingularProjection S B := by
  funext i j
  simp only [Matrix.sub_apply]
  unfold leftSingularProjection
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  simp only [Matrix.sub_apply]; ring

private theorem right_add {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r)
    (A B : RealMatrix n1 n2) :
    rightSingularProjection S (A + B)
      = rightSingularProjection S A + rightSingularProjection S B := by
  funext i j
  simp only [Matrix.add_apply]
  unfold rightSingularProjection
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  simp only [Matrix.add_apply]; ring

private theorem right_sub {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r)
    (A B : RealMatrix n1 n2) :
    rightSingularProjection S (A - B)
      = rightSingularProjection S A - rightSingularProjection S B := by
  funext i j
  simp only [Matrix.sub_apply]
  unfold rightSingularProjection
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  simp only [Matrix.sub_apply]; ring

private theorem two_add {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r)
    (A B : RealMatrix n1 n2) :
    twoSidedSingularProjection S (A + B)
      = twoSidedSingularProjection S A + twoSidedSingularProjection S B := by
  funext i j
  simp only [Matrix.add_apply]
  unfold twoSidedSingularProjection
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  simp only [Matrix.add_apply]; ring

private theorem two_sub {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r)
    (A B : RealMatrix n1 n2) :
    twoSidedSingularProjection S (A - B)
      = twoSidedSingularProjection S A - twoSidedSingularProjection S B := by
  funext i j
  simp only [Matrix.sub_apply]
  unfold twoSidedSingularProjection
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  simp only [Matrix.sub_apply]; ring

/-- `tangentProjection` is additive over subtraction (needed for L3). -/
theorem tangentProjection_sub {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r)
    (A B : RealMatrix n1 n2) :
    tangentProjection S (A - B) = tangentProjection S A - tangentProjection S B := by
  unfold tangentProjection
  rw [left_sub, right_sub, two_sub]
  abel

/-! ## L1: self-adjointness of tangentProjection -/

theorem tangentProjection_selfAdjoint {n1 n2 r : Nat} {M : RealMatrix n1 n2}
    (S : SVD M r) (X Y : RealMatrix n1 n2) :
    matrixInner (tangentProjection S X) Y = matrixInner X (tangentProjection S Y) := by
  unfold tangentProjection
  -- LHS: inner (L X + R X - T X) Y.  Flip via comm, expand with right-linearity.
  rw [matrixInner_comm (leftSingularProjection S X + rightSingularProjection S X
        - twoSidedSingularProjection S X) Y]
  rw [matrixInner_sub_right, matrixInner_add_right]
  -- RHS: inner X (L Y + R Y - T Y).  Expand with right-linearity.
  rw [matrixInner_sub_right, matrixInner_add_right]
  -- Now LHS: inner Y (LX)+inner Y (RX)-inner Y (TX)
  --     RHS: inner X (LY)+inner X (RY)-inner X (TY)
  rw [matrixInner_comm Y (leftSingularProjection S X),
      matrixInner_comm Y (rightSingularProjection S X),
      matrixInner_comm Y (twoSidedSingularProjection S X)]
  rw [leftSingularProjection_selfAdjoint, rightSingularProjection_selfAdjoint,
      twoSidedSingularProjection_selfAdjoint]

/-! ## L2: idempotency of tangentProjection

`P_T = L + R - T2`.  Using the composition relations
`LL=L, RR=R, LR=RL=T2, L·T2=T2·L=R·T2=T2·R=T2·T2=T2`,
expanding `P_T (P_T X)` gives `L + R - T2 = P_T`. -/

theorem tangentProjection_idem {n1 n2 r : Nat} {M : RealMatrix n1 n2}
    (S : SVD M r) (X : RealMatrix n1 n2) :
    tangentProjection S (tangentProjection S X) = tangentProjection S X := by
  -- Abbreviate the three projection outputs of X.
  set L := leftSingularProjection S X with hLdef
  set R := rightSingularProjection S X with hRdef
  set T := twoSidedSingularProjection S X with hTdef
  -- P_T (P_T X) = P_T (L + R - T)
  conv_lhs => rw [show tangentProjection S X = L + R - T from rfl]
  unfold tangentProjection
  -- left/right/two of (L + R - T)
  rw [left_sub, left_add, right_sub, right_add, two_sub, two_add]
  -- Now expand each projection-of-a-projection using the composition lemmas.
  rw [hLdef, hRdef, hTdef]
  rw [LL S X, LR S X, LT2 S X,
      RL S X, RR S X, RT2 S X,
      T2L S X, T2R S X, T2T2 S X]
  -- Goal: (L + T2 - T2) + (T2 + R - T2) - (T2 + T2 - T2) = L + R - T2  (as matrices)
  -- where now L,R,T2 are the concrete projections of X. Close by abel.
  abel

/-! ## L3: off-diagonal kernel = tangent-tangent inner product -/

theorem tangentCoordinateKernel_eq_proj_inner {n1 n2 r : Nat} {M : RealMatrix n1 n2}
    (S : SVD M r) (i : Fin n1) (j : Fin n2) (a : Fin n1) (b : Fin n2) :
    tangentCoordinateKernel S i j a b
      = matrixInner (tangentProjection S (coordinateMatrix i j))
          (tangentProjection S (coordinateMatrix a b)) := by
  unfold tangentCoordinateKernel
  -- Write e_ab = P_T e_ab + (e_ab - P_T e_ab).
  have hsplit : (coordinateMatrix a b : RealMatrix n1 n2)
      = tangentProjection S (coordinateMatrix a b)
        + (coordinateMatrix a b - tangentProjection S (coordinateMatrix a b)) := by
    abel
  conv_lhs => rw [hsplit]
  rw [matrixInner_add_right]
  -- The cross term inner (P_T e_ij) (e_ab - P_T e_ab) = 0.
  have hcross : matrixInner (tangentProjection S (coordinateMatrix i j))
      (coordinateMatrix a b - tangentProjection S (coordinateMatrix a b)) = 0 := by
    rw [tangentProjection_selfAdjoint S (coordinateMatrix i j)
          (coordinateMatrix a b - tangentProjection S (coordinateMatrix a b))]
    rw [tangentProjection_sub, tangentProjection_idem]
    rw [sub_self, matrixInner_zero_right]
  rw [hcross, add_zero]

/-! ## Base-bound layer (T0–T3)

Cauchy–Schwarz for `matrixInner`, the off-diagonal kernel magnitude bound, and the
entry-sup / Frobenius bounds for the kernel-square base matrix. -/

/-- Probing a matrix with a coordinate matrix reads off the entry. -/
theorem matrixInner_coordinateMatrix {n1 n2 : Nat} (X : RealMatrix n1 n2)
    (i : Fin n1) (j : Fin n2) :
    matrixInner X (coordinateMatrix i j) = X i j := by
  unfold matrixInner coordinateMatrix
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; exact absurd (Finset.mem_univ j) h
  · intro a _ ha
    refine Finset.sum_eq_zero (fun b _ => ?_)
    simp [ha]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- The kernel `K(w, ·)` reads off the entries of `P_T e_w`. -/
theorem tangentCoordinateKernel_eq_entry {n1 n2 r : Nat} {M : RealMatrix n1 n2}
    (S : SVD M r) (a : Fin n1) (b : Fin n2) (i : Fin n1) (j : Fin n2) :
    tangentCoordinateKernel S a b i j
      = (tangentProjection S (coordinateMatrix a b)) i j := by
  unfold tangentCoordinateKernel
  rw [matrixInner_coordinateMatrix]

/-! ### T0: Cauchy–Schwarz for the Frobenius inner product -/

theorem matrixInner_le_frob {n1 n2 : Nat} (X Y : RealMatrix n1 n2) :
    |matrixInner X Y| ≤ frobeniusNorm X * frobeniusNorm Y := by
  -- Flatten the double sums to single sums over the product index type.
  have hinner : matrixInner X Y
      = ∑ p : Fin n1 × Fin n2, X p.1 p.2 * Y p.1 p.2 := by
    unfold matrixInner
    rw [← Finset.sum_product']; rfl
  have hX : frobeniusNormSq X = ∑ p : Fin n1 × Fin n2, (X p.1 p.2) ^ 2 := by
    unfold frobeniusNormSq
    rw [← Finset.sum_product']; rfl
  have hY : frobeniusNormSq Y = ∑ p : Fin n1 × Fin n2, (Y p.1 p.2) ^ 2 := by
    unfold frobeniusNormSq
    rw [← Finset.sum_product']; rfl
  -- Cauchy–Schwarz (squared form).
  have hcs : (matrixInner X Y) ^ 2 ≤ frobeniusNormSq X * frobeniusNormSq Y := by
    rw [hinner, hX, hY]
    exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun p : Fin n1 × Fin n2 => X p.1 p.2) (fun p : Fin n1 × Fin n2 => Y p.1 p.2)
  -- Pass to absolute values / square roots.
  have hXnn : 0 ≤ frobeniusNormSq X := by
    rw [hX]; exact Finset.sum_nonneg (fun p _ => sq_nonneg _)
  have hYnn : 0 ≤ frobeniusNormSq Y := by
    rw [hY]; exact Finset.sum_nonneg (fun p _ => sq_nonneg _)
  unfold frobeniusNorm
  rw [← Real.sqrt_mul hXnn]
  -- |matrixInner X Y| = sqrt ((matrixInner X Y)^2) ≤ sqrt (frobNormSq X * frobNormSq Y)
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt hcs

/-! ### T1: off-diagonal kernel magnitude -/

theorem offdiag_kernel_mag {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r)
    (Cker : ℝ)
    (hdiag : ∀ a b, |tangentCoordinateKernel S a b a b| ≤ Cker) (hCker : 0 ≤ Cker)
    (hfrob : ∀ i j, frobeniusNormSq (tangentProjection S (coordinateMatrix i j))
        = tangentCoordinateKernel S i j i j)
    (i : Fin n1) (j : Fin n2) (a : Fin n1) (b : Fin n2) :
    |tangentCoordinateKernel S i j a b| ≤ Cker := by
  -- |K i j a b| = |⟨P_T e_ij, P_T e_ab⟩| ≤ ‖P_T e_ij‖ · ‖P_T e_ab‖.
  rw [tangentCoordinateKernel_eq_proj_inner]
  refine le_trans (matrixInner_le_frob _ _) ?_
  -- ‖P_T e_ij‖ = sqrt (K_diag i j), and K_diag i j ≤ Cker.
  have key : ∀ (x : Fin n1) (y : Fin n2),
      frobeniusNorm (tangentProjection S (coordinateMatrix x y)) ≤ Real.sqrt Cker := by
    intro x y
    unfold frobeniusNorm
    rw [hfrob x y]
    refine Real.sqrt_le_sqrt ?_
    have := hdiag x y
    exact le_trans (le_abs_self _) this
  calc frobeniusNorm (tangentProjection S (coordinateMatrix i j))
          * frobeniusNorm (tangentProjection S (coordinateMatrix a b))
        ≤ Real.sqrt Cker * Real.sqrt Cker := by
          apply mul_le_mul (key i j) (key a b) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = Cker := Real.mul_self_sqrt hCker

/-! ### T2: kernel-square base entry-sup bound -/

theorem base_entrysup {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r) (Cker : ℝ)
    (hdiag : ∀ a b, |tangentCoordinateKernel S a b a b| ≤ Cker) (hCker : 0 ≤ Cker)
    (hfrob : ∀ i j, frobeniusNormSq (tangentProjection S (coordinateMatrix i j))
        = tangentCoordinateKernel S i j i j)
    (w1 : Fin n1 × Fin n2) :
    entrySupNorm (quadraticMiddleIndexDistinctKernelSquareBaseMatrix S w1) ≤ Cker ^ 2 := by
  have hCker2 : (0 : ℝ) ≤ Cker ^ 2 := sq_nonneg _
  -- Each entry has |·| ≤ Cker^2.
  have hentry : ∀ (i : Fin n1) (j : Fin n2),
      |quadraticMiddleIndexDistinctKernelSquareBaseMatrix S w1 i j| ≤ Cker ^ 2 := by
    intro i j
    unfold quadraticMiddleIndexDistinctKernelSquareBaseMatrix
    by_cases h : (i, j) = w1
    · simp [h, hCker2]
    · rw [if_neg h, abs_mul, sq]
      exact mul_le_mul
        (offdiag_kernel_mag S Cker hdiag hCker hfrob w1.1 w1.2 i j)
        (offdiag_kernel_mag S Cker hdiag hCker hfrob i j w1.1 w1.2)
        (abs_nonneg _) hCker
  -- Bound the double iSup.
  unfold entrySupNorm
  refine Real.iSup_le (fun i => ?_) hCker2
  refine Real.iSup_le (fun j => ?_) hCker2
  exact hentry i j

/-! ### T3: kernel-square base Frobenius bound -/

theorem base_frob {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r) (Cker : ℝ)
    (hdiag : ∀ a b, |tangentCoordinateKernel S a b a b| ≤ Cker) (hCker : 0 ≤ Cker)
    (hfrob : ∀ i j, frobeniusNormSq (tangentProjection S (coordinateMatrix i j))
        = tangentCoordinateKernel S i j i j)
    (w1 : Fin n1 × Fin n2) :
    frobeniusNorm (quadraticMiddleIndexDistinctKernelSquareBaseMatrix S w1)
      ≤ Real.sqrt (Cker ^ 3) := by
  -- ‖base‖²_F ≤ Cker^3, then take sqrt.
  have hsq : frobeniusNormSq (quadraticMiddleIndexDistinctKernelSquareBaseMatrix S w1)
      ≤ Cker ^ 3 := by
    unfold frobeniusNormSq
    -- entry^2 ≤ Cker^2 * K(w1, ij)^2, pointwise.
    have hpt : ∀ (i : Fin n1) (j : Fin n2),
        (quadraticMiddleIndexDistinctKernelSquareBaseMatrix S w1 i j) ^ 2
          ≤ Cker ^ 2 * (tangentCoordinateKernel S w1.1 w1.2 i j) ^ 2 := by
      intro i j
      unfold quadraticMiddleIndexDistinctKernelSquareBaseMatrix
      by_cases h : (i, j) = w1
      · rw [if_pos h, zero_pow (by norm_num)]
        positivity
      · rw [if_neg h, mul_pow]
        -- K(w1,ij)^2 * K(ij,w1)^2 ≤ Cker^2 * K(w1,ij)^2
        have hKle : (tangentCoordinateKernel S i j w1.1 w1.2) ^ 2 ≤ Cker ^ 2 := by
          have := offdiag_kernel_mag S Cker hdiag hCker hfrob i j w1.1 w1.2
          rw [← sq_abs (tangentCoordinateKernel S i j w1.1 w1.2)]
          exact pow_le_pow_left₀ (abs_nonneg _) this 2
        rw [mul_comm (tangentCoordinateKernel S w1.1 w1.2 i j ^ 2)]
        exact mul_le_mul_of_nonneg_right hKle (sq_nonneg _)
    -- Sum the pointwise bound.
    calc (∑ i, ∑ j, (quadraticMiddleIndexDistinctKernelSquareBaseMatrix S w1 i j) ^ 2)
          ≤ ∑ i, ∑ j, Cker ^ 2 * (tangentCoordinateKernel S w1.1 w1.2 i j) ^ 2 := by
            refine Finset.sum_le_sum (fun i _ => ?_)
            refine Finset.sum_le_sum (fun j _ => ?_)
            exact hpt i j
      _ = Cker ^ 2 * ∑ i, ∑ j, (tangentCoordinateKernel S w1.1 w1.2 i j) ^ 2 := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun i _ => ?_)
            rw [Finset.mul_sum]
      _ = Cker ^ 2 * frobeniusNormSq (tangentProjection S (coordinateMatrix w1.1 w1.2)) := by
            congr 1
            unfold frobeniusNormSq
            refine Finset.sum_congr rfl (fun i _ => ?_)
            refine Finset.sum_congr rfl (fun j _ => ?_)
            -- K(w1, ij) = (P_T e_w1) i j
            rw [tangentCoordinateKernel_eq_entry]
      _ = Cker ^ 2 * tangentCoordinateKernel S w1.1 w1.2 w1.1 w1.2 := by
            rw [hfrob w1.1 w1.2]
      _ ≤ Cker ^ 2 * Cker := by
            refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
            exact le_trans (le_abs_self _) (hdiag w1.1 w1.2)
      _ = Cker ^ 3 := by ring
  -- frobeniusNorm = sqrt frobeniusNormSq ≤ sqrt (Cker^3).
  unfold frobeniusNorm
  exact Real.sqrt_le_sqrt hsq



end MatrixCompletion

open MatrixCompletion

/-- Off-diagonal tangent-kernel magnitude bound (CR2009 §6 eq (6.1)+(6.2)),
generalizing the diagonal eq (4.8) brick to ALL index pairs via Cauchy–Schwarz. -/
theorem solution :
    ∃ Cker : ℝ, 0 < Cker ∧
      ∀ (n₁ n₂ r : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → 1 ≤ μ₀ → A0 S μ₀ →
        ∀ i j a b,
          |tangentCoordinateKernel S i j a b| ≤
            Cker * μ₀ * ((r : ℝ) / (↑(min n₁ n₂))) := by
  obtain ⟨Cker, hCkerpos, hbrick⟩ :=
    tangent_coordinate_kernel_diagonal_bound_from_a0_min_dim
  refine ⟨Cker, hCkerpos, ?_⟩
  intro n₁ n₂ r M μ₀ S hn₁ hn₂ hr hμ₀ hA0 i j a b
  set D : ℝ := Cker * μ₀ * ((r : ℝ) / (↑(min n₁ n₂))) with hD
  have hμ₀pos : (0 : ℝ) < μ₀ := lt_of_lt_of_le one_pos hμ₀
  have hmin_pos : 0 < min n₁ n₂ := lt_min hn₁ hn₂
  have hDnn : 0 ≤ D := by
    rw [hD]
    have h1 : 0 ≤ Cker * μ₀ := mul_nonneg (le_of_lt hCkerpos) (le_of_lt hμ₀pos)
    apply mul_nonneg h1
    apply div_nonneg (Nat.cast_nonneg r)
    exact Nat.cast_nonneg _
  have hdiag : ∀ (x : Fin n₁) (y : Fin n₂),
      |tangentCoordinateKernel S x y x y| ≤ D := by
    intro x y
    rw [hD]
    exact hbrick n₁ n₂ r M μ₀ S hn₁ hn₂ hr hμ₀ hA0 x y
  have hfrob : ∀ (x : Fin n₁) (y : Fin n₂),
      frobeniusNormSq (tangentProjection S (coordinateMatrix x y))
        = tangentCoordinateKernel S x y x y := by
    intro x y
    rw [tangentCoordinateKernel_eq_proj_inner S x y x y]
    unfold frobeniusNormSq matrixInner
    refine Finset.sum_congr rfl (fun p _ => ?_)
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [sq]
  exact offdiag_kernel_mag S D hdiag hDnn hfrob i j a b

#print axioms solution
