-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_existsUnique_hom_sigma_of_disjoint_iSup_eq_top
-- name    : AlgebraicGeometry.Scheme.existsUnique_hom_sigma_of_disjoint_iSup_eq_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/10ec36d8-3bb5-5c90-a778-2bb23c249f8f
-- title:
--   Morphisms to a coproduct from a disjoint open cover
-- statement:
--   Let $\sigma$ be a type and $H : \sigma \to \mathrm{Scheme}$ a family of schemes, let $T$ be a scheme, and let $U : \sigma \to T.\mathrm{Opens}$ be a family of open subsets of $T$. Assume that the family is pairwise disjoint, i.e. $U_i \sqcap U_j = \bot$ whenever $i \neq j$ (disjointness in the lattice of opens of $T$), and that it covers $T$, i.e. $\bigsqcup_i U_i = \top$. Assume further given, for each $i$, a morphism of schemes $v_i$ from the open subscheme associated with $U_i$ to $H_i$. The conclusion is that there is exactly one morphism $u : T \to \coprod_i H_i$ into the coproduct of the family $H$ such that for every $i$ the composite of the open immersion $(U_i).\iota : U_i \to T$ with $u$ equals the composite of $v_i$ with the coproduct inclusion $\mathrm{Sigma}.\iota\, H\, i : H_i \to \coprod_i H_i$; that is, $u$ restricted to $U_i$ factors as $v_i$ followed by the $i$-th inclusion, and $u$ is uniquely determined by these restrictions.
--
--   This is the gluing half of the description of $T$-points of a coproduct of schemes: a decomposition of $T$ into pairwise disjoint opens covering it, together with a morphism from each piece to the corresponding member of the family, is the same thing as a single morphism to the coproduct. It is used in the identification of points of a disjoint union of Hilbert functors $\coprod_P \mathrm{Hilb}^P$, where a family is cut into the clopen pieces on which the Hilbert polynomial is constant.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_existsUnique_hom_sigma_of_disjoint_iSup_eq_top.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

theorem AlgebraicGeometry.Scheme.existsUnique_hom_sigma_of_disjoint_iSup_eq_top
    {σ : Type u} (H : σ → Scheme.{u}) {T : Scheme.{u}} (U : σ → T.Opens)
    (hdisj : ∀ i j, i ≠ j → Disjoint (U i) (U j)) (hcov : (⨆ i, U i) = ⊤)
    (v : ∀ i, ((U i : T.Opens) : Scheme.{u}) ⟶ H i) :
    ∃! u : T ⟶ ∐ H, ∀ i, (U i).ι ≫ u = v i ≫ Sigma.ι H i := by sorry
