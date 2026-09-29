-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_RatPair_v_evalAt_lt_of_forall_v_evalAt_add_evalAt_lt_on_sphere
-- name    : CerednikDrinfeld.Omega.RatPair.v_evalAt_lt_of_forall_v_evalAt_add_evalAt_lt_on_sphere
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/cce00dac-f2a5-5a40-b359-33af35b02348
-- title:
--   Orthogonality of inner and outer parts on a sphere
-- statement:
--   Let $K$ be an algebraically closed field carrying a valuation $v =$ `Valued.v` with values in a linearly ordered commutative group with zero $\Gamma_0$. Let $A$ and $B$ be pairs of polynomials over $K$, each consisting of a numerator and a denominator, evaluated at $z$ as the quotient $A.\mathrm{num}(z)/A.\mathrm{den}(z)$, let $t_0, \pi_0 \in K$ with $\pi_0 \neq 0$, and let $Z$ be a finite subset of $K$. Assume: $A.\mathrm{den}$ has no zero at any $z$ with $v(\pi_0) \le v(z - t_0)$; $\deg A.\mathrm{num} < \deg A.\mathrm{den}$; $B.\mathrm{den}$ has no zero at any $z$ with $v(z - t_0) < v(\pi_0)$; and $B.\mathrm{den}(z) \neq 0$ at every $z$ on the sphere $v(z - t_0) = v(\pi_0)$ satisfying $v(\pi_0) \le v(z - \zeta)$ for all $\zeta \in Z$ (call such $z$ generic). Assume finally that $b \in K$ satisfies $v\big(A(z) + B(z)\big) < v(b)$ at every generic point $z$ of the sphere. The conclusion is the conjunction: $v(A(z)) < v(b)$ whenever $v(\pi_0) \le v(z - t_0)$, and $v(B(z)) < v(b)$ whenever $v(z - t_0) < v(\pi_0)$.
--
--   This is the non-archimedean orthogonality of a Mittag-Leffler decomposition: a bound for the sum of an inner and an outer rational part at the generic points of a sphere propagates separately to each part on its own side, the inner part on the closed exterior disc and the outer part on the open disc. It rests on the additivity-as-maximum of Gauss norms for rational functions with separated poles, [`CerednikDrinfeld.Omega.gaussNorm_add_eq_max_of_separated_poles`](thm.html#CerednikDrinfeld.Omega.gaussNorm_add_eq_max_of_separated_poles), and is used in the construction of holomorphic functions on the Drinfeld upper half plane, via [`CerednikDrinfeld.Omega.mem_holOn_union_of_mem_holOn_of_forall_le_of_forall_mem_or_lt`](thm.html#CerednikDrinfeld.Omega.mem_holOn_union_of_mem_holOn_of_forall_le_of_forall_mem_or_lt), where principal parts of uniformly convergent sequences must be controlled.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_RatPair_v_evalAt_lt_of_forall_v_evalAt_add_evalAt_lt_on_sphere.lean

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Mathlib.FieldTheory.IsAlgClosed.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.RatPair.v_evalAt_lt_of_forall_v_evalAt_add_evalAt_lt_on_sphere
    (K : Type) [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [IsAlgClosed K]
    (A B : RatPair K) (t₀ π₀ : K) (hπ₀ : π₀ ≠ 0) (Z : Finset K)
    (hA : A.IsPoleFreeOn {z | Valued.v π₀ ≤ Valued.v (z - t₀)})
    (hA0 : A.num.degree < A.den.degree)
    (hB : B.IsPoleFreeOn {z | Valued.v (z - t₀) < Valued.v π₀})
    (hBC : ∀ z : K, Valued.v (z - t₀) = Valued.v π₀ → (∀ ζ ∈ Z, Valued.v π₀ ≤ Valued.v (z - ζ)) → B.den.eval z ≠ 0)
    (b : K)
    (hb : ∀ z : K, Valued.v (z - t₀) = Valued.v π₀ → (∀ ζ ∈ Z, Valued.v π₀ ≤ Valued.v (z - ζ)) →
      Valued.v (A.evalAt z + B.evalAt z) < Valued.v b) :
    (∀ z : K, Valued.v π₀ ≤ Valued.v (z - t₀) → Valued.v (A.evalAt z) < Valued.v b) ∧
    (∀ z : K, Valued.v (z - t₀) < Valued.v π₀ → Valued.v (B.evalAt z) < Valued.v b) := by sorry
