-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_exists_forall_v_apply_eq_on_circle_of_mem_holOn
-- name    : CerednikDrinfeld.Omega.exists_forall_v_apply_eq_on_circle_of_mem_holOn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/b59e63f5-c8a1-57f4-88ae-b51ae5542257
-- title:
--   Constant valuation of a holomorphic function on a circle
-- statement:
--   Let $K$ be an algebraically closed field carrying a valuation $v$ with values in a linearly ordered commutative group with zero $\Gamma_0$, let $S \subseteq K$ and let $f \colon S \to K$ belong to the subring $\mathrm{holOn}\ K\ S$, i.e. there is a sequence of pairs of polynomials (rational functions) $r_k$, each free of poles on $S$, with the values $r_k(z)$ for $k \in \mathbb{N}$ and $z \in S$ uniformly bounded in valuation by a single $b \in K$, such that $z \mapsto r_k(z)$ converges uniformly on $S$ to $f$. Fix $c, R \in K$ with $R \neq 0$ and a finite set $E \subseteq K$, and call $z \in K$ good when $v(z - c) = v(R)$ and $v(z - e) \ge v(R)$ for all $e \in E$ (the circle of radius $v(R)$ about $c$, with the open residue discs around the points of $E$ removed). Assume every good point of $K$ lies in $S$, and that $f(z_0) \neq 0$ for at least one good $z_0 \in S$. Then there are $s \in K$ with $s \neq 0$ and a finite set $Z \subseteq K$ such that $v(f(z)) \le v(s)$ for every good $z \in S$, with equality $v(f(z)) = v(s)$ whenever in addition $v(z - \zeta) \ge v(R)$ for all $\zeta \in Z$.
--
--   This is the maximum principle on a circle in non-archimedean analysis, in the form stating that the valuation of a nonzero holomorphic function is constant on the circle outside finitely many residue classes, and is bounded by that constant value everywhere on the circle. It is used to invert nowhere-vanishing holomorphic functions and to prove finiteness of the zero set of a holomorphic function on an affinoid and on a punctured open disc.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_exists_forall_v_apply_eq_on_circle_of_mem_holOn.lean

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Mathlib.FieldTheory.IsAlgClosed.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.exists_forall_v_apply_eq_on_circle_of_mem_holOn
    (K : Type) [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [IsAlgClosed K]
    {S : Set K} {f : ↥S → K} (hf : f ∈ holOn K S)
    (c R : K) (hR : R ≠ 0) (E : Finset K)
    (hS : ∀ z : K, Valued.v (z - c) = Valued.v R → (∀ e ∈ E, Valued.v R ≤ Valued.v (z - e)) → z ∈ S)
    (h₀ : ∃ z : ↥S, Valued.v ((z : K) - c) = Valued.v R ∧ (∀ e ∈ E, Valued.v R ≤ Valued.v ((z : K) - e)) ∧ f z ≠ 0) :
    ∃ s : K, s ≠ 0 ∧ ∃ Z : Finset K,
      (∀ z : ↥S, Valued.v ((z : K) - c) = Valued.v R → (∀ e ∈ E, Valued.v R ≤ Valued.v ((z : K) - e)) →
        Valued.v (f z) ≤ Valued.v s) ∧
      (∀ z : ↥S, Valued.v ((z : K) - c) = Valued.v R → (∀ e ∈ E, Valued.v R ≤ Valued.v ((z : K) - e)) →
        (∀ ζ ∈ Z, Valued.v R ≤ Valued.v ((z : K) - ζ)) → Valued.v (f z) = Valued.v s) := by sorry
