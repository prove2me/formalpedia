-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_existsUnique_iso_forall_pullback_mapIso_eq_of_iSup_eq_top
-- name    : AlgebraicGeometry.Scheme.Modules.existsUnique_iso_forall_pullback_mapIso_eq_of_iSup_eq_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/e065618c-3d71-5a08-9bac-0deac865e647
-- title:
--   Gluing isomorphisms of mathcal O_X-modules along a basis-like cover
-- statement:
--   Let $X$ be a scheme and let $M$, $N$ be sheaves of $\mathcal O_X$-modules on $X$ (objects of `X.Modules`). Let $U : \iota \to$ `X.Opens` be a family of open subsets of $X$, indexed by a type $\iota$ in an arbitrary universe, such that $\bigsqcup_i U_i = \top$, and such that the family is basis-like in the following sense: for all $i, j$ one has $U_i \cap U_j \le \bigsqcup_k U_k$, the supremum being taken over those indices $k$ with $U_k \le U_i \cap U_j$. Suppose given, for each $i$, an isomorphism $e_i \colon \iota_i^* M \cong \iota_i^* N$ of modules on $U_i$, where $\iota_i = (U_i).\iota$ is the inclusion of the open subscheme $U_i$ into $X$ and $\iota_i^*$ is `Scheme.Modules.pullback`. Suppose further that these are compatible with restriction to smaller members of the family: whenever $U_j \le U_i$, the pullback of $e_i$ along the inclusion `X.homOfLE h` $\colon U_j \to U_i$ agrees with $e_j$ after transport by the canonical identification of $($`X.homOfLE h`$)^*\iota_i^*$ with $\iota_j^*$ given by `Scheme.Modules.pullbackComp` followed by `Scheme.Modules.pullbackCongr` applied to `X.homOfLE_ι h`, evaluated at $M$ and at $N$. Then there is a unique isomorphism $f \colon M \cong N$ of $\mathcal O_X$-modules whose pullback $\iota_i^* f$ equals $e_i$ for every $i$.
--
--   This is the gluing (descent) statement for isomorphisms of sheaves of modules, in the form in which locally constructed isomorphisms actually arise: charts indexed by a basis-like cover, with compatibility imposed only for nested pairs of charts rather than on pairwise intersections. It is obtained from the corresponding gluing statement for morphisms, [`AlgebraicGeometry.Scheme.Modules.existsUnique_hom_app_eq_of_iSup_eq_top`](thm.html#AlgebraicGeometry.Scheme.Modules.existsUnique_hom_app_eq_of_iSup_eq_top), and is used in the Čech trivialisation lemmas and in recognising invertible modules that are locally trivial.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_existsUnique_iso_forall_pullback_mapIso_eq_of_iSup_eq_top.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory Opposite AlgebraicGeometry

universe u v

theorem AlgebraicGeometry.Scheme.Modules.existsUnique_iso_forall_pullback_mapIso_eq_of_iSup_eq_top
    {X : Scheme.{u}} (M N : X.Modules) {ι : Type v} (U : ι → X.Opens) (hU : ⨆ i, U i = ⊤)
    (hB : ∀ i j, U i ⊓ U j ≤ ⨆ (k : {k : ι // U k ≤ U i ⊓ U j}), U k.1)
    (e : ∀ i, (Scheme.Modules.pullback (U i).ι).obj M ≅ (Scheme.Modules.pullback (U i).ι).obj N)
    (he : ∀ (i j : ι) (h : U j ≤ U i),
      (Scheme.Modules.pullback (X.homOfLE h)).mapIso (e i) =
        ((Scheme.Modules.pullbackComp (X.homOfLE h) (U i).ι).app M ≪≫
            (Scheme.Modules.pullbackCongr (X.homOfLE_ι h)).app M) ≪≫
          e j ≪≫
          ((Scheme.Modules.pullbackComp (X.homOfLE h) (U i).ι).app N ≪≫
            (Scheme.Modules.pullbackCongr (X.homOfLE_ι h)).app N).symm) :
    ∃! f : M ≅ N, ∀ i, (Scheme.Modules.pullback (U i).ι).mapIso f = e i := by sorry
