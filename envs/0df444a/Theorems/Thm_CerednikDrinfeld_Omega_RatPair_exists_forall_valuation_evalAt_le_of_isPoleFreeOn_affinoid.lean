-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_RatPair_exists_forall_valuation_evalAt_le_of_isPoleFreeOn_affinoid
-- name    : CerednikDrinfeld.Omega.RatPair.exists_forall_valuation_evalAt_le_of_isPoleFreeOn_affinoid
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/cc7ee154-7368-55ca-8001-c015af062897
-- title:
--   Pole-free rational functions are bounded on the affinoids Ωₙ
-- statement:
--   Let $K_0$ and $K$ be fields with $K$ an algebra over $K_0$, let $\Gamma_0$ be a linearly ordered commutative group with zero and let $K$ carry a valuation $v =$ `Valued.v` with values in $\Gamma_0$, with $K$ algebraically closed. Let $\varpi$ be a pseudo-uniformiser of $K_0$ relative to $K$, that is, an element $\varpi\in K_0$ whose image in $K$ satisfies $0 < v(\varpi) < 1$ and such that for every nonzero $a\in K_0$ there is $N\in\mathbb{N}$ with $v(\varpi)^N \le v(a) \le v(\varpi)^{-N}$. Fix $n\in\mathbb{N}$ and write $\Omega_n =$ `affinoid ϖ n` for the set of $z\in K$ with $v(z)\le v(\varpi)^{-n}$ and $v(z - a)\ge v(\varpi)^{n}$ for every $a\in K_0$ with $v(a)\le v(\varpi)^{-n}$. Let $r$ be a pair of polynomials over $K$, with components `r.num` and `r.den`, and assume `r.IsPoleFreeOn` holds on $\Omega_n$, i.e. `r.den.eval z ≠ 0` for all $z\in\Omega_n$. Then there exists $b\in K$ such that $v\bigl(\mathrm{num}(z)/\mathrm{den}(z)\bigr)\le v(b)$ for all $z\in\Omega_n$, the quotient being `r.evalAt z`.
--
--   This is the boundedness assertion for rational functions without poles on the $n$-th affinoid in the standard exhaustion of Drinfeld's $p$-adic upper half plane, with the bound expressed as the valuation of an element of $K$ rather than by a real constant. It feeds the construction of holomorphic functions on these affinoids, and is used in the statement about holomorphic functions on affinoids attached to a Čerednik–Drinfeld quotient.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_RatPair_exists_forall_valuation_evalAt_le_of_isPoleFreeOn_affinoid.lean

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.RatPair.exists_forall_valuation_evalAt_le_of_isPoleFreeOn_affinoid
    {K₀ K : Type} [Field K₀] [Field K] [Algebra K₀ K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [IsAlgClosed K]
    (ϖ : PseudoUniformizer K₀ K) (n : ℕ) (r : RatPair K) (hr : r.IsPoleFreeOn (affinoid ϖ n)) :
    ∃ b : K, ∀ z ∈ affinoid ϖ n, Valued.v (r.evalAt z) ≤ Valued.v b := by sorry
