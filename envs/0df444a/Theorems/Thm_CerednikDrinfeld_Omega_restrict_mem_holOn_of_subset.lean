-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_restrict_mem_holOn_of_subset
-- name    : CerednikDrinfeld.Omega.restrict_mem_holOn_of_subset
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/0f458ade-6ca6-51d7-954a-acd3989b3f4a
-- title:
--   Restriction of holomorphic functions to a subset
-- statement:
--   Let $K$ be a field equipped with a valuation with values in a linearly ordered commutative group with zero $\Gamma_0$, and let $T \subseteq S$ be subsets of $K$. Let $f : S \to K$ belong to the subring $\mathrm{holOn}\ K\ S$, that is, suppose $f$ satisfies `IsHolOn`: there is a sequence $r : \mathbb{N} \to \mathrm{RatPair}\ K$ of pairs of polynomials such that each $r_k$ is pole-free on $S$, the evaluations are uniformly bounded in the sense that for some $b \in K$ one has $v((r_k).\mathrm{evalAt}\ z) \le v(b)$ for all $k$ and all $z \in S$, and the functions $z \mapsto (r_k).\mathrm{evalAt}\ z$ converge uniformly on $S$ to $f$ as $k \to \infty$. The conclusion is that the function $T \to K$ sending $z$ to $f$ evaluated at the point $z$ regarded, via the inclusion $T \subseteq S$, as an element of $S$ lies in $\mathrm{holOn}\ K\ T$; that is, this restriction of $f$ is again a uniform limit on $T$ of a uniformly bounded sequence of rational functions pole-free on $T$.
--
--   This records that the rings of rigid-holomorphic functions attached to subsets of a valued field form a presheaf for inclusions: membership in $\mathrm{holOn}$ is stable under restriction. It is used in the reductions that pass from holomorphy on a chart piece, in particular on a disc, to holomorphy on a sub-piece, for instance in [`CerednikDrinfeld.Omega.exists_holRing_mul_eq_mul_and_apply_eq_of_holOn_disc`](thm.html#CerednikDrinfeld.Omega.exists_holRing_mul_eq_mul_and_apply_eq_of_holOn_disc) and in the statements about pulled-back sections over a cover.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_restrict_mem_holOn_of_subset.lean

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.restrict_mem_holOn_of_subset
    (K : Type) [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    {S T : Set K} (hTS : T ⊆ S) {f : ↥S → K} (hf : f ∈ holOn K S) :
    (fun z : ↥T => f ⟨(z : K), hTS z.2⟩) ∈ holOn K T := by sorry
