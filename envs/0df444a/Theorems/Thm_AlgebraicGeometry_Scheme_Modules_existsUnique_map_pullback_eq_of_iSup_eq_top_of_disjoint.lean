-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_existsUnique_map_pullback_eq_of_iSup_eq_top_of_disjoint
-- name    : AlgebraicGeometry.Scheme.Modules.existsUnique_map_pullback_eq_of_iSup_eq_top_of_disjoint
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/4f6f6f98-f430-5631-862e-0ebed1f60720
-- title:
--   Unique gluing of module maps along a disjoint open cover
-- statement:
--   Let $Y$ be a scheme and let $U : \iota \to Y.\mathrm{Opens}$ be a family of open subsets of $Y$ indexed by an arbitrary type $\iota$, subject to two hypotheses: the supremum $\bigsqcup_i U_i$ is the whole of $Y$, and $U_i \sqcap U_j = \bot$ whenever $i \neq j$, i.e. the $U_i$ cover $Y$ and are pairwise disjoint. Let $L_1, L_2$ be two objects of $Y.\mathrm{Modules}$, the category of sheaves of $\mathcal{O}_Y$-modules on $Y$, and suppose given, for every index $i$, a morphism $\varphi_i$ from the restriction of $L_1$ to $U_i$ to the restriction of $L_2$ to $U_i$, restriction being the pullback functor `Scheme.Modules.pullback` along the canonical open immersion $(U_i).\iota : U_i \to Y$. The conclusion is that there exists a unique morphism $\Phi : L_1 \to L_2$ of $\mathcal{O}_Y$-modules whose restriction along $(U_i).\iota$ equals $\varphi_i$ for every $i$. No compatibility condition on the family $(\varphi_i)$ is imposed, the cover being disjoint.
--
--   This is the gluing of morphisms of sheaves of modules along an open cover, in the special case of a pairwise disjoint cover, where the usual agreement condition on overlaps is vacuous. It serves the construction of morphisms and isomorphisms of $\mathcal{O}_Y$-modules from local data on a disjoint decomposition of the base, and is used in establishing the existence of isomorphisms to pullbacks in `exists_iso_pullback_forall_mapIso_eq_of_free_of_split` and `nonempty_iso_of_forall_nonempty_pullback_iso_of_isPullback_pi`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_existsUnique_map_pullback_eq_of_iSup_eq_top_of_disjoint.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe v u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.existsUnique_map_pullback_eq_of_iSup_eq_top_of_disjoint
    {Y : Scheme.{u}} {ι : Type v} (U : ι → Y.Opens) (hU : ⨆ i, U i = ⊤)
    (hdisj : ∀ i j, i ≠ j → U i ⊓ U j = ⊥) (L₁ L₂ : Y.Modules)
    (φ : ∀ i, (Scheme.Modules.pullback (U i).ι).obj L₁ ⟶ (Scheme.Modules.pullback (U i).ι).obj L₂) :
    ∃! Φ : L₁ ⟶ L₂, ∀ i, (Scheme.Modules.pullback (U i).ι).map Φ = φ i := by sorry
