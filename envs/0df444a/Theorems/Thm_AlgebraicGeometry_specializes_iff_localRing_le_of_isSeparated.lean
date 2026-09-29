-- Prove2me | Theorems.Thm_AlgebraicGeometry_specializes_iff_localRing_le_of_isSeparated
-- name    : AlgebraicGeometry.specializes_iff_localRing_le_of_isSeparated
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/e0878f11-cfc2-5e63-af67-16b672de6784
-- title:
--   Specialisation detected by local rings, for separated integral schemes
-- statement:
--   Let $A_0$ be a commutative ring, let $X$ be a scheme (in the smallest universe) equipped with a morphism `toBase` to $\operatorname{Spec} A_0$, and assume $X$ is integral and that `toBase` is separated. Let $F$ be a field together with a ring isomorphism $\varphi : F \cong K(X)$ onto the function field of $X$ (the stalk of the structure sheaf at the generic point), and let $x,y$ be points of $X$. For a point $z$ of $X$, the project's `SemistableModel.localRing X φ z` is the subring of $F$ obtained as the range of the composite $\varphi^{-1}\circ(\text{canonical map } \mathcal O_{X,z}\to K(X))$, i.e. the copy inside $F$ of the image of the local ring $\mathcal O_{X,z}$ in the function field. The assertion is an equivalence: $x$ specialises to $y$ (that is, $y$ lies in the closure of $\{x\}$, written $x \rightsquigarrow y$) if and only if the subring of $F$ attached to $y$ is contained in the subring of $F$ attached to $x$, $\mathcal O_{X,y}\subseteq \mathcal O_{X,x}$ read inside $F$. Note that separatedness of `toBase` over the affine base is needed only for the implication from the inclusion of local rings to the specialisation.
--
--   This is the standard description of the specialisation order on an integral separated scheme by inclusion of local rings inside the function field (as in EGA I 8.2). It is used in the assembly of a semistable model of the full-level modular curve from affine charts, where points have to be identified and their closure relations determined from the valuation-theoretic data of their local rings; the separatedness half is deduced from the project's uniqueness statement [`AlgebraicGeometry.Scheme.eq_of_forall_mem_valuationSubring_of_isSeparated`](thm.html#AlgebraicGeometry.Scheme.eq_of_forall_mem_valuationSubring_of_isSeparated).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_specializes_iff_localRing_le_of_isSeparated.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry IsLocalRing AlgebraicCurve

theorem AlgebraicGeometry.specializes_iff_localRing_le_of_isSeparated
    (A₀ : Type) [CommRing A₀]
    (X : Scheme.{0}) (toBase : X ⟶ Spec (CommRingCat.of A₀)) [IsIntegral X] [IsSeparated toBase]
    {F : Type} [Field F] (φ : F ≃+* X.functionField) (x y : X) :
    x ⤳ y ↔ SemistableModel.localRing X φ y ≤ SemistableModel.localRing X φ x := by sorry
