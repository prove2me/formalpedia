-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_toDescentData_map_bijective_of_openCover
-- name    : AlgebraicGeometry.Scheme.Modules.toDescentData_map_bijective_of_openCover
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/8d880a86-be29-560b-86dd-ca8d1b69e922
-- title:
--   Full faithfulness of restriction to an open cover for 𝒪-modules
-- statement:
--   Let $Y$ be a scheme, let $\iota$ be an index type (in a universe independent of that of the schemes), and let $V : \iota \to \mathbf{Sch}$ be a family of schemes equipped with morphisms $g_i \colon V_i \to Y$, each of which is an open immersion. Assume the family is jointly surjective on points: for every point $y$ of $Y$ there is an index $i$ with $y$ in the set-theoretic range of the underlying continuous map of $g_i$. Let $L_1, L_2$ be two sheaves of $\mathcal O_Y$-modules, i.e. objects of `Y.Modules`. Consider the pseudofunctor `Scheme.Modules.pseudofunctor` sending a scheme $X$ to its category of $\mathcal O_X$-modules, composed with `Bicategory.Adj.forget₁` so as to retain the pull-back direction of each adjunction, and the associated descent-data functor attached to the family $(g_i)_i$. The theorem asserts that the induced map on morphisms $(L_1 \to L_2) \to \bigl(\text{descent data of } L_1 \to \text{descent data of } L_2\bigr)$, which sends a morphism to the family of its pull-backs together with the induced compatibilities, is bijective; that is, the descent-data functor is fully faithful on the pair $(L_1, L_2)$.
--
--   This is the prestack, or full faithfulness, half of Zariski descent for sheaves of modules: a morphism of $\mathcal O_Y$-modules is determined by, and can be glued from, a compatible family of morphisms on the members of an open cover, with no quasi-coherence hypothesis. It is used to construct morphisms and isomorphisms of line bundles and of rigidified line bundles from local data, for instance in the comparison of pull-backs along covers in the treatment of the relative Picard functor and of Riemann forms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_toDescentData_map_bijective_of_openCover.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe v u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.toDescentData_map_bijective_of_openCover
    {Y : Scheme.{u}} {ι : Type v} {V : ι → Scheme.{u}} (g : ∀ i, V i ⟶ Y) [∀ i, IsOpenImmersion (g i)]
    (hg : ∀ y : Y, ∃ i, y ∈ Set.range (g i).base) (L₁ L₂ : Y.Modules) :
    Function.Bijective
      ((((Scheme.Modules.pseudofunctor.{u}).comp Bicategory.Adj.forget₁).toDescentData g).map : (L₁ ⟶ L₂) → _) := by sorry
