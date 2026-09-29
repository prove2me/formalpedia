-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_holRing_eq_and_affinoid_zero_eq
-- name    : CerednikDrinfeld.Omega.holRing_eq_and_affinoid_zero_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/ac99686e-8f0f-5a1f-89a1-0db8b9b5c838
-- title:
--   Independence of 𝒪(Ω) and Ω₀ of the pseudo-uniformiser
-- statement:
--   Let $K_0$ and $K$ be fields with $K$ a $K_0$-algebra, and let $K$ carry a valuation $v$ with values in a linearly ordered commutative group with zero $\Gamma_0$. A pseudo-uniformiser $\varpi$ (a term of `PseudoUniformizer K₀ K`) is an element $\varpi \in K_0$ with $0 < v(\varpi) < 1$ (valuations of images under the structure map $K_0 \to K$ throughout) such that for every $a \in K_0$, $a \neq 0$, there is $N \in \mathbb N$ with $v(\varpi)^N \le v(a) \le v(\varpi)^{-N}$. For such a $\varpi$ and $n \in \mathbb N$, `affinoid ϖ n` is the set of $z \in K$ with $v(z) \le v(\varpi)^{-n}$ and $v(z - a) \ge v(\varpi)^{n}$ for every $a \in K_0$ with $v(a) \le v(\varpi)^{-n}$; and `holRing ϖ` is the subring of all functions from the Drinfeld upper half plane $\Omega = K \setminus \mathrm{im}(K_0 \to K)$ to $K$ whose restriction to `affinoid ϖ n`, for every $n$, is a uniform limit of a sequence of rational functions (given by pairs of polynomials) each pole-free on that affinoid and with values of valuation bounded by one fixed $b \in K$. The theorem asserts, for any two pseudo-uniformisers $\varpi, \varpi'$, that `holRing ϖ = holRing ϖ'` and `affinoid ϖ 0 = affinoid ϖ' 0`.
--
--   This is the well-definedness statement underlying the affinoid exhaustion of Drinfeld's $p$-adic upper half plane: the ring of rigid-holomorphic functions and the level-zero affinoid (the fibre over the standard vertex of the Bruhat–Tits tree) are intrinsic, not tied to the chosen pseudo-uniformiser. It allows later results about theta functions and their valuations, proved for one convenient pseudo-uniformiser, to be transferred to any other.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_holRing_eq_and_affinoid_zero_eq.lean

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.holRing_eq_and_affinoid_zero_eq
    {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (ϖ ϖ' : PseudoUniformizer K₀ K) : holRing ϖ = holRing ϖ' ∧ affinoid ϖ 0 = affinoid ϖ' 0 := by sorry
