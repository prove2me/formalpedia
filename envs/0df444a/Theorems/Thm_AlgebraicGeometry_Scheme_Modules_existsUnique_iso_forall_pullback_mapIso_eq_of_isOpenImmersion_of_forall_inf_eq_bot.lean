-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_existsUnique_iso_forall_pullback_mapIso_eq_of_isOpenImmersion_of_forall_inf_eq_bot
-- name    : AlgebraicGeometry.Scheme.Modules.existsUnique_iso_forall_pullback_mapIso_eq_of_isOpenImmersion_of_forall_inf_eq_bot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/70e8e94a-8ca4-545b-818d-aa981cfebb80
-- title:
--   Gluing module isomorphisms along disjoint covering open immersions
-- statement:
--   Let $X$ be a scheme and let $M, N$ be objects of `X.Modules`, the category of sheaves of $\mathcal{O}_X$-modules. Let $\iota$ be an index type, let $Y_j$ be schemes for $j \in \iota$, and let $b_j \colon Y_j \to X$ be morphisms, each an open immersion. Assume the open subschemes cut out by the images cover $X$, in the sense that the supremum $\bigsqcup_j \operatorname{opensRange}(b_j)$ of the open ranges is $\top$ in the lattice of opens of $X$, and that the family is pairwise disjoint: $\operatorname{opensRange}(b_j) \sqcap \operatorname{opensRange}(b_l) = \bot$ whenever $j \neq l$. Suppose given, for each $j$, an isomorphism $e_j \colon b_j^{*}M \xrightarrow{\ \sim\ } b_j^{*}N$ in `(Y j).Modules`, where $b_j^{*}$ denotes the pullback functor `Scheme.Modules.pullback (b j)`. Then there is a unique isomorphism $\varphi \colon M \xrightarrow{\ \sim\ } N$ of $\mathcal{O}_X$-modules such that for every $j$ the isomorphism obtained by applying $b_j^{*}$ to $\varphi$ equals $e_j$, as an equality of isomorphisms (not merely of their underlying morphisms).
--
--   This is the gluing statement for isomorphisms of quasi-coherent-style module sheaves along a decomposition of a scheme into pairwise disjoint opens, stated for an arbitrary family of open immersions rather than for a family of open subschemes. It is used in the construction of theta-type points, in [`AlgebraicGeometry.Polarisation.ThetaPt.exists_pt_eq_comp_act_eq_of_isIdempotentElem_of_sum_eq_one`](thm.html#AlgebraicGeometry.Polarisation.ThetaPt.exists_pt_eq_comp_act_eq_of_isIdempotentElem_of_sum_eq_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_existsUnique_iso_forall_pullback_mapIso_eq_of_isOpenImmersion_of_forall_inf_eq_bot.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory Opposite AlgebraicGeometry

universe u v

theorem AlgebraicGeometry.Scheme.Modules.existsUnique_iso_forall_pullback_mapIso_eq_of_isOpenImmersion_of_forall_inf_eq_bot
    {X : Scheme.{u}} (M N : X.Modules) {ι : Type v} {Y : ι → Scheme.{u}} (b : ∀ j, Y j ⟶ X)
    [∀ j, IsOpenImmersion (b j)]
    (hcov : ⨆ j, Scheme.Hom.opensRange (b j) = ⊤)
    (hdisj : ∀ j l, j ≠ l → Scheme.Hom.opensRange (b j) ⊓ Scheme.Hom.opensRange (b l) = ⊥)
    (e : ∀ j, (Scheme.Modules.pullback (b j)).obj M ≅ (Scheme.Modules.pullback (b j)).obj N) :
    ∃! φ : M ≅ N, ∀ j, (Scheme.Modules.pullback (b j)).mapIso φ = e j := by sorry
