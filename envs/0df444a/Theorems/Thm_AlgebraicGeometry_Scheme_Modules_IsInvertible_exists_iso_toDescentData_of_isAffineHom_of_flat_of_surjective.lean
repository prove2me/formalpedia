-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_iso_toDescentData_of_isAffineHom_of_flat_of_surjective
-- name    : AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_iso_toDescentData_of_isAffineHom_of_flat_of_surjective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/607bbbe6-98ab-546b-8143-e10a5264aef3
-- title:
--   Effective descent for invertible modules along affine flat surjections
-- statement:
--   Let $q\colon Y'\to Y$ be a morphism of schemes (in a fixed universe) which is an affine morphism, flat and surjective, and let $D$ be a descent datum for the pseudofunctor $X\mapsto \mathbf{Mod}(\mathcal O_X)$, $f\mapsto f^{*}$ (the pseudofunctor `Scheme.Modules.pseudofunctor` composed with `Bicategory.Adj.forget₁`, so that only the pullback functors are retained) relative to the one-element family of arrows $\mathrm{Unit}\to(q)$, i.e. relative to $q$ alone. Assume that for each index $i$ the underlying module $D.\mathrm{obj}\,i$ on $Y'$ is invertible in the sense of the project's predicate `Scheme.Modules.IsInvertible`: for every point of the scheme in question there is an open neighbourhood $U$ such that the pullback of the module along the inclusion $U\hookrightarrow$ the scheme is isomorphic to the unit module $\mathcal O_U$ on $U$. Then there exists a module $L$ on $Y$ which is invertible in the same sense, together with an isomorphism of descent data between the canonical descent datum obtained from $L$ (the image of $L$ under `toDescentData` for the family $\mathrm{Unit}\to(q)$) and $D$; the isomorphism is asserted through the nonemptiness of the type of such isomorphisms.
--
--   This is effectivity of fpqc descent for line bundles along an affine, flat, surjective morphism, in the form needed to construct line bundles on a base from line bundles with descent data on a cover. It is used in the treatment of the relative Picard functor and of rigidified line bundles, and in the descent arguments for polarisations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_iso_toDescentData_of_isAffineHom_of_flat_of_surjective.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_iso_toDescentData_of_isAffineHom_of_flat_of_surjective
    {Y Y' : Scheme.{u}} (q : Y' ⟶ Y) [IsAffineHom q] [Flat q] [Surjective q]
    (D : ((Scheme.Modules.pseudofunctor.{u}).comp Bicategory.Adj.forget₁).DescentData (fun _ : Unit => q))
    (hD : ∀ i, Scheme.Modules.IsInvertible (D.obj i)) :
    ∃ L : Y.Modules, Scheme.Modules.IsInvertible L ∧
      Nonempty ((((Scheme.Modules.pseudofunctor.{u}).comp Bicategory.Adj.forget₁).toDescentData
        (fun _ : Unit => q)).obj L ≅ D) := by sorry
