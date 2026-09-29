-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_normModule_unit_iso
-- name    : AlgebraicGeometry.Scheme.Modules.nonempty_normModule_unit_iso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/2fd3324f-4e4e-5272-b2cf-b30ac706b9a4
-- title:
--   Norm of the unit module along a finite flat map
-- statement:
--   Let $X$ and $Y$ be schemes (in a fixed universe) and let $\pi \colon X \to Y$ be a morphism that is finite, flat and locally of finite presentation. Let $d$ be a natural number and assume that the fibre rank $\pi.\mathrm{finrank}\ y$ equals $d$ at every point $y$ of $Y$. The assertion is that the type of isomorphisms $\mathrm{normModule}\ \pi\ d\,(\mathbf 1_{X.\mathrm{Modules}}) \cong \mathbf 1_{Y.\mathrm{Modules}}$ in the monoidal category of modules on $Y$ is nonempty; that is, such an isomorphism exists, though none is named. Here, by definition, $\mathrm{normModule}\ \pi\ d\ L$ is $\det_d((\pi_*)L) \otimes \mathrm{dual}\bigl(\det_d((\pi_*)\mathbf 1_{X.\mathrm{Modules}})\bigr)$, with $\mathrm{dual}\ M = (\mathrm{ihom}\ M).\mathrm{obj}\,(\mathbf 1)$ the internal hom into the unit object. Taking $L$ to be the unit module on $X$, the conclusion therefore says that, writing $P = \det_d(\pi_*\mathcal O_X)$, there is an isomorphism $P \otimes P^{\vee} \cong \mathcal O_Y$ of modules on $Y$.
--
--   This is the unit (zero-section) half of the statement that the norm construction along a finite flat morphism of constant rank $d$ is multiplicative on invertible modules: the norm of the structure sheaf is the structure sheaf. It is used in the relative Picard part of the development, where the norm morphism between schemes representing relative Picard functors must be seen to respect the zero section and the multiplicative structure.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_nonempty_normModule_unit_iso.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_RigidifiedLineBundleOfInvertible
import Definitions.Def_AlgebraicGeometry_ModulesNormModule
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra
  GoodReductionJacobian AlgebraicGeometry.RelPicard

universe u

set_option maxHeartbeats 800000 in

theorem AlgebraicGeometry.Scheme.Modules.nonempty_normModule_unit_iso
    {X Y : Scheme.{u}} (π : X ⟶ Y) [IsFinite π] [Flat π] [LocallyOfFinitePresentation π]
    (d : ℕ) (hd : ∀ y : Y, π.finrank y = d) :
    Nonempty (Scheme.Modules.normModule π d (𝟙_ X.Modules) ≅ 𝟙_ Y.Modules) := by sorry
