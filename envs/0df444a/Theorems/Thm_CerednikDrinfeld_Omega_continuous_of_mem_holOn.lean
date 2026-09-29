-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_continuous_of_mem_holOn
-- name    : CerednikDrinfeld.Omega.continuous_of_mem_holOn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/701f7228-04b1-5446-93ba-a640e0a6a82e
-- title:
--   Continuity of functions holomorphic by rational approximation
-- statement:
--   Let $K$ be a field carrying a valuation with values in a linearly ordered commutative group with zero $\Gamma_0$, so that $K$ is topologised by that valuation, let $S \subseteq K$ be an arbitrary subset, and let $g \colon S \to K$ be a function on the subtype $S$. Assume $g$ lies in the subring `holOn K S` of $S \to K$, that is, $g$ satisfies `IsHolOn K S`: there is a sequence $k \mapsto r_k$ of rational pairs over $K$ (each $r_k$ given by a numerator and a denominator polynomial, with associated evaluation $r_k(z) = \mathrm{num}(z)/\mathrm{den}(z)$) such that each $r_k$ is pole-free on $S$, the values are uniformly bounded in the sense that there exists $b \in K$ with $v(r_k(z)) \le v(b)$ for all $k$ and all $z \in S$, and the functions $z \mapsto r_k(z)$ converge to $g$ uniformly on $S$ along the filter at infinity on $\mathbb{N}$. The conclusion is that $g$ is continuous for the subspace topology on $S$ and the valuation topology on $K$.
--
--   This is the elementary continuity statement for functions holomorphic on a subset of a valued field in the sense of uniform approximation by pole-free rational functions, the analogue of the classical fact that a uniform limit of continuous functions is continuous. It is used where continuity of such functions is needed, namely in the construction of a holomorphic inverse for a nowhere-vanishing element of `holOn` and in the statement relating the theta function on $\Omega$ to its periods.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_continuous_of_mem_holOn.lean

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.continuous_of_mem_holOn
    (K : Type) [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    {S : Set K} {g : ↥S → K} (hg : g ∈ holOn K S) :
    Continuous g := by sorry
