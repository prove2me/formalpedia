-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_thetaMultipliable_of_isDiscrete_of_isExhausted
-- name    : CerednikDrinfeld.Omega.thetaMultipliable_of_isDiscrete_of_isExhausted
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/29a57904-8ea3-5f33-9f1b-4a9678bc8dd0
-- title:
--   Theta product converges on all of Ω for discrete ρ
-- statement:
--   Let $K_0$ be a field and $K$ a $K_0$-algebra which is a field, equipped with a valuation $v$ taking values in a linearly ordered commutative group with zero $\Gamma_0$ and complete for the induced topology. Let $\varpi$ be a pseudo-uniformiser of $K_0$ relative to $K$, that is, an element $\varpi \in K_0$ with $0 < v(\varpi) < 1$ in $K$ such that every nonzero $a \in K_0$ satisfies $v(\varpi)^N \le v(a) \le v(\varpi)^{-N}$ for some $N \in \mathbb{N}$, and assume $\varpi$ is exhausting: every $z$ in $\Omega = K \setminus \mathrm{image}(K_0 \to K)$ lies in one of the affinoids $\mathrm{affinoid}\ \varpi\ n = \{z : v(z) \le v(\varpi)^{-n}$ and $v(z - a) \ge v(\varpi)^{n}$ for all $a \in K_0$ with $v(a) \le v(\varpi)^{-n}\}$. Let $G$ be a group and $\rho : G \to \mathrm{PGL}_2(K_0)$ a homomorphism which is discrete in the sense that for every $\varepsilon \neq 0$ in $\Gamma_0$ the set of $\gamma \in G$ such that $\rho(\gamma)$ admits a lift $g \in \mathrm{GL}_2(K_0)$ with all entries of valuation $\le 1$ and $v(\det g) \ge \varepsilon$ is finite. Then for any four points $a, b, z_0, z \in \Omega$ the family $\gamma \mapsto [z, z_0; \rho(\gamma)a, \rho(\gamma)b]$ of cross-ratios, with $\rho(\gamma)$ acting by Möbius transformations, is multipliable over $G$.
--
--   This is the convergence statement for the theta product $\Theta(a,b;z_0;z) = \prod_{\gamma \in G} [z, z_0; \gamma a, \gamma b]$ attached to a discrete subgroup of $\mathrm{PGL}_2(K_0)$ acting on Drinfeld's upper half plane, in the unrestricted form where the four points range over all of $\Omega$ rather than over a single affinoid. It supplies the multipliability hypothesis used downstream in the construction of theta functions, their automorphy multipliers and the period pairing of a Mumford quotient.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_thetaMultipliable_of_isDiscrete_of_isExhausted.lean

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_CerednikDrinfeld_DiscreteProjectiveAction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.thetaMultipliable_of_isDiscrete_of_isExhausted
    {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K]
    (ϖ : PseudoUniformizer K₀ K) (hex : IsExhausted ϖ)
    {G : Type} [Group G] (ρ : G →* PGL(2, K₀)) (hρ : IsDiscrete K ρ)
    {a b z₀ z : K} (ha : a ∈ upperHalfPlane K₀ K) (hb : b ∈ upperHalfPlane K₀ K)
    (hz₀ : z₀ ∈ upperHalfPlane K₀ K) (hz : z ∈ upperHalfPlane K₀ K) :
    ThetaMultipliable ρ a b z₀ z := by sorry
