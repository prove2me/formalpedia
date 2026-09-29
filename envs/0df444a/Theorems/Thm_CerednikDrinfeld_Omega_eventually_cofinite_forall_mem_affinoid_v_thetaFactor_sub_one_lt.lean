-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_eventually_cofinite_forall_mem_affinoid_v_thetaFactor_sub_one_lt
-- name    : CerednikDrinfeld.Omega.eventually_cofinite_forall_mem_affinoid_v_thetaFactor_sub_one_lt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/95c52380-9f2c-5a0b-92c2-92c52ddd1f45
-- title:
--   Theta factors tend to 1 uniformly on affinoids
-- statement:
--   Let $K_0$ be a field and $K$ a field equipped with a $K_0$-algebra structure and a valuation $v$ with values in a linearly ordered commutative group with zero $\Gamma_0$. Let $\varpi$ be a pseudo-uniformiser, i.e. an element of $K_0$ with $0 < v(\varpi) < 1$ such that every nonzero $a \in K_0$ satisfies $v(\varpi)^N \le v(a) \le v(\varpi)^{-N}$ for some $N \in \mathbb{N}$ (valuations of elements of $K_0$ taken after the structure map to $K$). Let $G$ be a group and $\rho : G \to \mathrm{PGL}_2(K_0)$ a homomorphism satisfying `IsDiscrete`: for every $\varepsilon \ne 0$ in $\Gamma_0$, only finitely many $\gamma \in G$ admit a representative $g \in \mathrm{GL}_2(K_0)$ of $\rho(\gamma)$ all of whose entries have valuation $\le 1$ and with $v(\det g) \ge \varepsilon$. Fix $n \in \mathbb{N}$ and let $\Omega_n =$ `affinoid ϖ n` be the set of $z \in K$ with $v(z) \le v(\varpi)^{-n}$ and $v(z - a) \ge v(\varpi)^{n}$ for every $a \in K_0$ with $v(a) \le v(\varpi)^{-n}$. Let $a, b, z_0 \in \Omega_n$ and let $\varepsilon \ne 0$ in $\Gamma_0$. Then for all but finitely many $\gamma \in G$ one has, simultaneously for all $z \in \Omega_n$,
--   $$v\bigl([z, z_0; \rho(\gamma)a, \rho(\gamma)b] - 1\bigr) < \varepsilon,$$
--   where the theta factor is the cross-ratio $((z - x)(z_0 - y))/((z - y)(z_0 - x))$ with $x, y$ the images of $a, b$ under the Möbius action of $\rho(\gamma)$ on $K \cup \{\infty\}$ read back in $K$.
--
--   This is the uniform-convergence estimate underlying the construction of theta functions for a discrete subgroup of $\mathrm{PGL}_2(K_0)$ acting on the Drinfeld upper half plane: the factors of the infinite product defining $\theta(a,b;z)$ approach $1$ uniformly on each affinoid $\Omega_n$ outside a finite set of group elements. It is used in the construction of theta quotients and their periods, for instance by [`CerednikDrinfeld.Omega.exists_holRing_div_eq_theta`](thm.html#CerednikDrinfeld.Omega.exists_holRing_div_eq_theta) and [`CerednikDrinfeld.Omega.exists_isUnit_coe_eq_thetaMer_apply_smul_eq_period_mul`](thm.html#CerednikDrinfeld.Omega.exists_isUnit_coe_eq_thetaMer_apply_smul_eq_period_mul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_eventually_cofinite_forall_mem_affinoid_v_thetaFactor_sub_one_lt.lean

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_CerednikDrinfeld_DiscreteProjectiveAction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
open Filter CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.eventually_cofinite_forall_mem_affinoid_v_thetaFactor_sub_one_lt
    {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (ϖ : PseudoUniformizer K₀ K) {G : Type} [Group G] (ρ : G →* PGL(2, K₀)) (hρ : IsDiscrete K ρ)
    (n : ℕ) {a b z₀ : K} (ha : a ∈ affinoid ϖ n) (hb : b ∈ affinoid ϖ n) (hz₀ : z₀ ∈ affinoid ϖ n)
    (ε : Γ₀) (hε : ε ≠ 0) :
    ∀ᶠ γ in cofinite, ∀ z ∈ affinoid ϖ n, Valued.v (thetaFactor ρ a b z₀ z γ - 1) < ε := by sorry
