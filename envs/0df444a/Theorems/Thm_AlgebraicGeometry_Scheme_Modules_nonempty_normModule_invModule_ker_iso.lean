-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_normModule_invModule_ker_iso
-- name    : AlgebraicGeometry.Scheme.Modules.nonempty_normModule_invModule_ker_iso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/1702ab1c-c97a-50b2-82ad-7bbc56e7db07
-- title:
--   Point formula for the norm of a rational point's line bundle
-- statement:
--   Let $K$ be a field, let $X$ and $X'$ be schemes, and let $t : X \to \operatorname{Spec} K$ and $t' : X' \to \operatorname{Spec} K$ be morphisms that are separated and smooth of relative dimension $1$. Let $\pi : X' \to X$ satisfy $t \circ \pi = t'$ and be finite, flat and locally of finite presentation, and let $d$ be a natural number with $\pi.\text{finrank}\, y = d$ for every point $y$ of $X$. Let $x'$ be a section of $t'$, that is, a morphism $q : \operatorname{Spec} K \to X'$ with $t' \circ q = \mathrm{id}$. For an ideal sheaf datum $I$ on a scheme, `module` $I$ is the kernel of the unit-to-pushforward-unit map attached to the closed immersion of the associated subscheme, and `invModule` $I$ is its dual, the internal hom from that module into the unit object of the monoidal category of modules. The assertion is that the category of $X$-modules contains an isomorphism between $\det_d\bigl(\pi_*((x')^{\mathrm{ker}})^{\vee}\bigr) \otimes \det_d(\pi_* \mathcal{O}_{X'})^{\vee}$, i.e. `normModule π d` applied to the inverse module of the ideal sheaf `x'.1.ker` of $x'$, and the inverse module of the ideal sheaf `(x'.1 ≫ π).ker` of the composite point $\pi \circ x'$ of $X$; the conclusion is phrased as `Nonempty` of the type of such isomorphisms.
--
--   This is the point formula for the norm of a line bundle along a finite locally free morphism, in the special case of the line bundle of a $K$-rational point on a smooth separated relative curve: the norm of $\mathcal{O}(x')$ is $\mathcal{O}(\pi x')$. It is used in the construction of norm maps on relative Picard functors and Abel–Jacobi sections, and thence in the treatment of correspondences on modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_nonempty_normModule_invModule_ker_iso.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_ModulesNormModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.nonempty_normModule_invModule_ker_iso
    {K : Type u} [Field K] {X X' : Scheme.{u}}
    (t : X ⟶ Spec (CommRingCat.of K)) (t' : X' ⟶ Spec (CommRingCat.of K))
    [IsSeparated t] [IsSeparated t'] [SmoothOfRelativeDimension 1 t] [SmoothOfRelativeDimension 1 t']
    (π : X' ⟶ X) (hπ : π ≫ t = t') [IsFinite π] [Flat π] [LocallyOfFinitePresentation π]
    (d : ℕ) (hd : ∀ y : X, π.finrank y = d)
    (x' : {q : Spec (CommRingCat.of K) ⟶ X' // q ≫ t' = 𝟙 _}) :
    Nonempty (Scheme.Modules.normModule π d (x'.1.ker).invModule ≅ ((x'.1 ≫ π).ker).invModule) := by sorry
