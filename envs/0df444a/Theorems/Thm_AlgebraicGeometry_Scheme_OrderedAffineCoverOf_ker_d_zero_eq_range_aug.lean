-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_OrderedAffineCoverOf_ker_d_zero_eq_range_aug
-- name    : AlgebraicGeometry.Scheme.OrderedAffineCoverOf.ker_d_zero_eq_range_aug
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/b471f409-03c1-5923-ac06-a2f1872b2358
-- title:
--   Čech H⁰ of the structure sheaf on an ordered affine cover
-- statement:
--   Let $R$ be a commutative ring, $V$ a scheme and $\pi\colon V\to\operatorname{Spec}R$ a morphism of schemes, let $W$ be an open subscheme of $V$, and let $K$ be an `OrderedAffineCoverOf` $W$: a finite, linearly ordered index type $\iota$ together with opens $U_i\subseteq V$ ($i\in\iota$) each of which is affine, satisfies $U_i\le W$, and with $\bigsqcup_i U_i=W$ as a supremum of opens. All modules of sections $\Gamma(V,O)$ are regarded as $R$-modules through the algebra structure `moduleSections` attached to $\pi$, namely the ring map obtained from the inverse of $\Gamma$–$\operatorname{Spec}$ adjunction isomorphism for $R$ followed by the component of $\pi$ from $\Gamma(\operatorname{Spec}R,\top)$ to $\Gamma(V,O)$. The assertion is the equality of two $R$-submodules of the module `K.cochain 0` of $0$-cochains, i.e. of families indexed by `K.Idx 0` of sections over the corresponding intersections: the kernel of the degree-zero Čech differential `K.d π 0`, with values in $1$-cochains, coincides with the range of the augmentation `K.aug π`, the $R$-linear map $\Gamma(V,W)\to$ `K.cochain 0` whose components are the restriction maps along the inclusions of those intersections into $W$.
--
--   This is the sheaf axiom (gluing plus uniqueness of the glued section is not asserted here, only the identification of the kernel with the image) for the structure sheaf on the cover $K$ of $W$, phrased for the alternating Čech complex: it identifies $\check H^0(K,\mathcal O)$ with the image of $\Gamma(V,W)$. It feeds the exactness statements for the augmented Čech complex and the rows of the Leray-type double complex used in the project, being cited by [`AlgebraicGeometry.OModulePresheaf.Leray.rows_exact`](thm.html#AlgebraicGeometry.OModulePresheaf.Leray.rows_exact) and the zigzag lemmas for cochains killed by the differential.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_OrderedAffineCoverOf_ker_d_zero_eq_range_aug.lean

import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.RingTheory.LocalProperties.Submodule
import Mathlib.RingTheory.Localization.Away.Basic
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.OrderedAffineCoverOf.ker_d_zero_eq_range_aug {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R)) {W : V.Opens} (K : V.OrderedAffineCoverOf W) : letI := Scheme.OrderedAffineCoverOf.moduleSections π; LinearMap.ker (K.d π 0) = LinearMap.range (K.aug π) := by sorry
