-- Prove2me | Theorems.Thm_AlgebraicGeometry_isPullback_of_iSup_eq_top
-- name    : AlgebraicGeometry.isPullback_of_iSup_eq_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/0f57fb3d-300c-5889-98a5-13a272640cfd
-- title:
--   Being cartesian is Zariski-local on one corner
-- statement:
--   Let $P$, $X$, $Y$, $Z$ be schemes and let $\mathrm{fst} : P \to X$, $\mathrm{snd} : P \to Y$, $f : X \to Z$, $g : Y \to Z$ be morphisms of schemes. Let $(U_i)_{i \in \iota}$ be a family of open subschemes of $X$, indexed by an arbitrary type, whose supremum in the lattice of opens of $X$ is $\top$, i.e. which covers $X$. Assume that for every index $i$ the square formed by the restriction $\mathrm{fst} \mid_{U_i} : \mathrm{fst}^{-1}(U_i) \to U_i$ of $\mathrm{fst}$, by the composite of the open immersion $\mathrm{fst}^{-1}(U_i) \hookrightarrow P$ with $\mathrm{snd}$, by the composite of the open immersion $U_i \hookrightarrow X$ with $f$, and by $g$, is a pullback square (in particular each such square commutes). Then the square formed by $\mathrm{fst}$, $\mathrm{snd}$, $f$, $g$ is itself a pullback square: $\mathrm{fst}$ followed by $f$ equals $\mathrm{snd}$ followed by $g$, and the resulting cone exhibits $P$ as $X \times_Z Y$. Note that commutativity of the large square is not assumed; it is part of the conclusion.
--
--   This is the statement that the property of a commutative square of schemes being cartesian may be checked locally on the corner $X$, over any open cover of $X$. It is used in the construction of étale lifts along nilpotent thickenings, namely by [`AlgebraicGeometry.exists_etale_isPullback_forall_existsUnique_comp_eq_of_isNilpotent`](thm.html#AlgebraicGeometry.exists_etale_isPullback_forall_existsUnique_comp_eq_of_isNilpotent), where a candidate pullback is built and recognised patch by patch.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_isPullback_of_iSup_eq_top.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v

theorem AlgebraicGeometry.isPullback_of_iSup_eq_top
    {P X Y Z : Scheme.{u}} (fst : P ⟶ X) (snd : P ⟶ Y) (f : X ⟶ Z) (g : Y ⟶ Z)
    {ι : Type v} (U : ι → X.Opens) (hU : ⨆ i, U i = ⊤)
    (h : ∀ i, IsPullback (fst ∣_ U i) ((fst ⁻¹ᵁ U i).ι ≫ snd) ((U i).ι ≫ f) g) :
    IsPullback fst snd f g := by sorry
