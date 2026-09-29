-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_exists_v_sub_sub_mul_le_mul_sq_of_mem_affinoid_zero
-- name    : CerednikDrinfeld.Omega.exists_v_sub_sub_mul_le_mul_sq_of_mem_affinoid_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/0c7d0e0f-829a-5f38-a37a-1cee82f2b0b9
-- title:
--   First-order Taylor estimate on the standard vertex affinoid
-- statement:
--   Let $K_0$ be a field and $K$ a $K_0$-algebra which is a field, carrying a valuation $v =$ `Valued.v` with values in a linearly ordered commutative group with zero $\Gamma_0$, and assume $K$ is complete and algebraically closed. Let $\varpi$ be a pseudo-uniformiser of $K_0$ relative to $K$, that is an element $\varpi \in K_0$ whose image in $K$ satisfies $0 < v(\varpi) < 1$ and such that every nonzero $a \in K_0$ satisfies $v(\varpi)^N \le v(a) \le v(\varpi)^{-N}$ for some $N \in \mathbb{N}$. Let $f$ belong to the subring `holRing` $\varpi$ of functions on $\Omega = K \setminus \mathrm{image}(K_0 \to K)$ whose restriction to each affinoid `affinoid` $\varpi\,n$ is a uniform limit of a sequence of rational functions that are pole-free on that affinoid and uniformly bounded in valuation there. Let $M \in \Gamma_0$ and suppose $v(f(z)) \le M$ for every $z \in \Omega$ lying in `affinoid` $\varpi\,0 = \{z : v(z) \le 1 \text{ and } v(z - a) \ge 1 \text{ for all } a \in K_0 \text{ with } v(a) \le 1\}$, and let $b \in \Omega$ lie in that same affinoid. Then there exists $d \in K$ with $v(d) \le M$ such that for every $z \in \Omega$ with $v(z - b) < 1$ one has $v\big(f(z) - f(b) - d\,(z-b)\big) \le M \cdot v(z-b)^2$.
--
--   This is the non-archimedean Cauchy estimate in the shape of a first-order Taylor expansion with quadratic remainder, on the open residue disc about a point of the standard vertex affinoid of Drinfeld's upper half plane: no derivative operator is introduced, the linear coefficient $d$ being produced together with the bound on the remainder. It is used in the construction and estimation of theta-products on the upper half plane, in particular by [`CerednikDrinfeld.Omega.exists_points_prod_theta_eq_of_v_sub_one_lt`](thm.html#CerednikDrinfeld.Omega.exists_points_prod_theta_eq_of_v_sub_one_lt) and [`CerednikDrinfeld.Omega.exists_v_sub_sum_div_sub_le_of_forall_eq_mul_prod_zpow_mul_one_add`](thm.html#CerednikDrinfeld.Omega.exists_v_sub_sum_div_sub_le_of_forall_eq_mul_prod_zpow_mul_one_add).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_exists_v_sub_sub_mul_le_mul_sq_of_mem_affinoid_zero.lean

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Mathlib.FieldTheory.IsAlgClosed.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.exists_v_sub_sub_mul_le_mul_sq_of_mem_affinoid_zero
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (ϖ : PseudoUniformizer K₀ K)
    (f : ↥(holRing ϖ)) (M : Γ₀)
    (hM : ∀ z : ↥(upperHalfPlane K₀ K), (z : K) ∈ affinoid ϖ 0 → Valued.v ((f : ↥(upperHalfPlane K₀ K) → K) z) ≤ M)
    (b : ↥(upperHalfPlane K₀ K)) (hb : (b : K) ∈ affinoid ϖ 0) :
    ∃ d : K, Valued.v d ≤ M ∧
      ∀ z : ↥(upperHalfPlane K₀ K), Valued.v ((z : K) - (b : K)) < 1 →
        Valued.v ((f : ↥(upperHalfPlane K₀ K) → K) z - (f : ↥(upperHalfPlane K₀ K) → K) b - d * ((z : K) - (b : K))) ≤
          M * Valued.v ((z : K) - (b : K)) ^ 2 := by sorry
