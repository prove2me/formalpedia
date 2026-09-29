-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_finite_setOf_pmoebius_mem_affinoid
-- name    : CerednikDrinfeld.Omega.finite_setOf_pmoebius_mem_affinoid
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/358108fe-8fef-5008-8d07-2c48d2c6499a
-- title:
--   Finiteness of {γ:ρ(γ)b∈Ωₙ} for discrete ρ
-- statement:
--   Let $K_0$ be a field and $K$ a field equipped with a $K_0$-algebra structure and with a valuation $v =$ `Valued.v` taking values in a linearly ordered commutative group with zero $\Gamma_0$. Let $\varpi$ be a pseudo-uniformiser, i.e. an element $\varpi.\varpi \in K_0$ whose image $q := v(\varpi.\varpi)$ in $K$ satisfies $0 < q < 1$ and such that every nonzero $a \in K_0$ admits $N \in \mathbb{N}$ with $q^N \le v(a) \le q^{-N}$. Let $G$ be a group and $\rho : G \to \mathrm{PGL}_2(K_0)$ a group homomorphism which is discrete in the sense of `IsDiscrete`: for every $\varepsilon \in \Gamma_0$, $\varepsilon \ne 0$, only finitely many $\gamma \in G$ admit a lift $g \in \mathrm{GL}_2(K_0)$ with $\mathrm{mk}\,g = \rho(\gamma)$, all entries of valuation $\le 1$, and $v(\det g) \ge \varepsilon$. Let $n \in \mathbb{N}$ and let $b \in K$ lie in `affinoid` $\varpi\,n$, that is $v(b) \le q^{-n}$ and $q^{n} \le v(b - a)$ for every $a \in K_0$ with $v(a) \le q^{-n}$. Then the set of $\gamma \in G$ such that `pmoebius` $K_0\,(\rho\,\gamma)\,b$ — the affine coordinate of the image of $b$ under the action of $\rho(\gamma)$ on $\mathbb{P}^1(K) =$ `OnePoint K`, with the value $0$ assigned at $\infty$ — again lies in `affinoid` $\varpi\,n$ is finite.
--
--   This is the discontinuity statement for a discrete subgroup of $\mathrm{PGL}_2(K_0)$ acting on Drinfeld's upper half-plane: an orbit meets each of the exhausting affinoids $\Omega_n$ in finitely many points, so orbits can accumulate only on $\mathbb{P}^1(K_0)$. It is what makes all but finitely many factors of a theta product pole-free on a given affinoid, and is used in the Mumford-curve/Čerednik–Drinfeld part of the development, in particular in the construction of period data and of divisor classes on the quotient curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_finite_setOf_pmoebius_mem_affinoid.lean

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_CerednikDrinfeld_DiscreteProjectiveAction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.finite_setOf_pmoebius_mem_affinoid
    {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (ϖ : PseudoUniformizer K₀ K) {G : Type} [Group G] (ρ : G →* PGL(2, K₀)) (hρ : IsDiscrete K ρ)
    (n : ℕ) {b : K} (hb : b ∈ affinoid ϖ n) :
    {γ : G | pmoebius K₀ (ρ γ) b ∈ affinoid ϖ n}.Finite := by sorry
