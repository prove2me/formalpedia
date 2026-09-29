-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_thetaMultipliable_of_isDiscrete_of_mem_affinoid
-- name    : CerednikDrinfeld.Omega.thetaMultipliable_of_isDiscrete_of_mem_affinoid
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/e3e85c6a-bffb-5659-90e4-75fdd2591cdf
-- title:
--   Multipliability of the cross-ratio theta product on an affinoid
-- statement:
--   Let $K_0$ be a field and $K$ a $K_0$-algebra which is a field, carrying a valuation $v$ with values in a linearly ordered commutative group with zero $\Gamma_0$ and complete for the associated topology. Let $\varpi$ be a pseudo-uniformiser for $K_0 \to K$, that is an element $\varpi.\varpi \in K_0$ whose image has $0 < v(\varpi.\varpi) < 1$ and such that every nonzero $a \in K_0$ satisfies $v(\varpi.\varpi)^N \le v(a) \le v(\varpi.\varpi)^{-N}$ for some $N \in \mathbb{N}$. Let $G$ be a group and $\rho \colon G \to \mathrm{PGL}(2, K_0)$ a group homomorphism satisfying `IsDiscrete K ρ`: for every nonzero $\varepsilon \in \Gamma_0$, the set of $\gamma \in G$ for which $\rho\gamma$ admits a lift $g \in \mathrm{GL}_2(K_0)$ with all entries of valuation $\le 1$ and with $v(\det g) \ge \varepsilon$ is finite. Fix $n \in \mathbb{N}$ and let $a, b, z_0, z$ all lie in `affinoid ϖ n`, the set of $w \in K$ with $v(w) \le v(\varpi.\varpi)^{-n}$ and $v(w - c) \ge v(\varpi.\varpi)^{n}$ for every $c \in K_0$ with $v(c) \le v(\varpi.\varpi)^{-n}$. Then the family of cross-ratios $\gamma \mapsto [z, z_0; \rho(\gamma)a, \rho(\gamma)b]$, where $\rho(\gamma)$ acts by the projective Möbius action `pmoebius`, is multipliable in $K$; that is, the theta product $\Theta(a,b;z_0;z) = \prod_{\gamma \in G} [z, z_0; \rho(\gamma)a, \rho(\gamma)b]$ converges unconditionally.
--
--   This is the basic convergence statement for the cross-ratio theta series attached to a discrete subgroup of $\mathrm{PGL}_2(K_0)$ acting on Drinfeld's $p$-adic upper half plane, in the case where all four points lie in one of the affinoids $\Omega_n$ of the standard exhaustion. It is the input to the construction of theta functions and their functional equations, and is used in particular to pass, by monotonicity and exhaustion, to arbitrary points of $\Omega$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_thetaMultipliable_of_isDiscrete_of_mem_affinoid.lean

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_CerednikDrinfeld_DiscreteProjectiveAction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.thetaMultipliable_of_isDiscrete_of_mem_affinoid
    {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K]
    (ϖ : PseudoUniformizer K₀ K) {G : Type} [Group G] (ρ : G →* PGL(2, K₀)) (hρ : IsDiscrete K ρ)
    (n : ℕ) {a b z₀ z : K} (ha : a ∈ affinoid ϖ n) (hb : b ∈ affinoid ϖ n) (hz₀ : z₀ ∈ affinoid ϖ n)
    (hz : z ∈ affinoid ϖ n) :
    ThetaMultipliable ρ a b z₀ z := by sorry
