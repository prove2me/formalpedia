-- Prove2me | Theorems.Thm_AlgebraicGeometry_isOpenImmersion_of_locallyQuasiFinite_of_isIntegrallyClosed_stalk_of_denseRange
-- name    : AlgebraicGeometry.isOpenImmersion_of_locallyQuasiFinite_of_isIntegrallyClosed_stalk_of_denseRange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/6bec144a-9352-5ef1-9dbf-5b64a84f9f93
-- title:
--   Birational form of Zariski's main theorem
-- statement:
--   Let $f\colon X \to Y$ be a morphism of schemes (in a fixed universe) which is locally quasi-finite, separated, locally of finite type and quasi-compact, with $X$ reduced and $Y$ locally Noetherian. Assume that for every point $y$ of $Y$ the local ring $\mathcal{O}_{Y,y}$, taken as the stalk of the structure presheaf, is an integral domain and is integrally closed in its fraction field. Assume further that there are an open subscheme $V \subseteq Y$ whose underlying set is dense in $Y$, and a morphism $s\colon V \to X$ from the scheme $V$ such that $s$ followed by $f$ equals the canonical open immersion $V \to Y$, and such that the map on underlying topological spaces induced by $s$ has dense range in $X$. Then $f$ is an open immersion.
--
--   This is the birational form of Zariski's main theorem as in Bosch–Lütkebohmert–Raynaud 2.3/Theorem 2′: a quasi-finite separated morphism with reduced source and normal locally Noetherian target which admits a section with dense image over a dense open of the target is an open immersion. It is used in the construction of Néron models, where it identifies a quasi-finite separated candidate as an open subscheme, and is invoked in assembling open immersions out of families of local sections.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_isOpenImmersion_of_locallyQuasiFinite_of_isIntegrallyClosed_stalk_of_denseRange.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

theorem AlgebraicGeometry.isOpenImmersion_of_locallyQuasiFinite_of_isIntegrallyClosed_stalk_of_denseRange
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyQuasiFinite f] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsReduced X] [IsLocallyNoetherian Y]
    (hY : ∀ y : Y, IsDomain (Y.presheaf.stalk y) ∧ IsIntegrallyClosed (Y.presheaf.stalk y))
    (V : Y.Opens) (hV : Dense (V : Set Y))
    (s : (V : Scheme.{u}) ⟶ X) (hs : s ≫ f = V.ι) (hsd : DenseRange s.base) :
    IsOpenImmersion f := by sorry
