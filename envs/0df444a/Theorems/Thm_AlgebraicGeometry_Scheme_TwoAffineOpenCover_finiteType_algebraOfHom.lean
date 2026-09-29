-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_finiteType_algebraOfHom
-- name    : AlgebraicGeometry.Scheme.TwoAffineOpenCover.finiteType_algebraOfHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/3ed9d14c-6647-5e4f-a4ed-14bb24dbca19
-- title:
--   Sections on an affine open form a finite type R-algebra
-- statement:
--   Let $R$ be a commutative ring in universe $u$, let $T$ be a scheme (also in universe $u$), and let $t \colon T \to \operatorname{Spec} R$ be a morphism to the spectrum of $R$, which is assumed to be locally of finite type in Mathlib's sense. Let $W$ be an open of $T$, and let $hW$ assert that $W$ is an affine open, i.e. the open subscheme determined by $W$ is affine. Then, with respect to the $R$-algebra structure on $\Gamma(T, W)$ furnished by `Scheme.TwoAffineOpenCover.algebraOfHom t W` — the ring homomorphism obtained by composing the inverse of the canonical isomorphism $R \cong \Gamma(\operatorname{Spec} R, \top)$ with the restriction map `t.appLE ⊤ W le_top` of $t$ from the total space of $\operatorname{Spec} R$ to $W$, regarded as making $\Gamma(T, W)$ into an $R$-algebra — the $R$-algebra $\Gamma(T, W)$ is of finite type, that is, finitely generated as an $R$-algebra. (The conclusion is stated under a local instance introducing exactly that algebra structure, so that it refers to the structure induced by $t$ and not to any other.)
--
--   This is the statement that 'locally of finite type' may be read off on affine opens: the ring of sections over an affine open of a scheme locally of finite type over $R$ is a finitely generated $R$-algebra. It is used to feed affine opens of such a base into results that require a finite type (hence, over a Noetherian ring, Noetherian) affine base, for instance in the treatment of relative Picard schemes, polarisations and cohomology of relative curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_finiteType_algebraOfHom.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.TwoAffineOpenCover.finiteType_algebraOfHom
    {R : Type u} [CommRing R] {T : Scheme.{u}} (t : T ⟶ Spec (.of R)) [LocallyOfFiniteType t]
    (W : T.Opens) (hW : IsAffineOpen W) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom t W
    Algebra.FiniteType R Γ(T, W) := by sorry
