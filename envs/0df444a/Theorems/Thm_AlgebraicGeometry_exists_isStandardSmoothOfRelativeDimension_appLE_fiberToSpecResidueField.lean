-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_isStandardSmoothOfRelativeDimension_appLE_fiberToSpecResidueField
-- name    : AlgebraicGeometry.exists_isStandardSmoothOfRelativeDimension_appLE_fiberToSpecResidueField
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/e005b922-b07c-5ac2-8912-9a1c1f061b20
-- title:
--   Standard-smooth charts restrict to charts on the fibre
-- statement:
--   Let $f : X \to Y$ be a morphism of schemes (in a fixed universe), $x$ a point of $X$, and $m$ a natural number. Suppose $U$ is an open subscheme of $Y$ which is affine, $V$ is an open subscheme of $X$ which is affine and contains $x$, and $V \le f^{-1}U$, so that $f$ induces a ring homomorphism $\Gamma(Y, U) \to \Gamma(X, V)$ (`f.appLE U V e`); assume this homomorphism is standard smooth of relative dimension $m$ in the sense of Mathlib's `RingHom.IsStandardSmoothOfRelativeDimension`. Write $y = f(x)$. The conclusion asserts the existence of an open subscheme $U'$ of $\operatorname{Spec} \kappa(y)$, where $\kappa(y)$ is the residue field of $Y$ at $y$, and of an open subscheme $V'$ of the fibre `f.fiber y` such that $V'$ is affine, the canonical point `f.asFiber x` of the fibre determined by $x$ lies in $V'$, $V'$ is contained in the preimage of $U'$ under the structure morphism `f.fiberToSpecResidueField y` from the fibre to $\operatorname{Spec} \kappa(y)$, and the induced ring homomorphism $\Gamma(\operatorname{Spec}\kappa(y), U') \to \Gamma(f^{-1}(y), V')$ is again standard smooth of relative dimension $m$.
--
--   This is the local form of the statement that a standard-smooth chart of relative dimension $m$ for $f$ at a point restricts, by base change to the residue field of the image point, to such a chart for the fibre through that point. It is used by [`AlgebraicGeometry.smoothOfRelativeDimension_of_smooth_of_forall_fiber`](thm.html#AlgebraicGeometry.smoothOfRelativeDimension_of_smooth_of_forall_fiber), the fibrewise criterion recognising a morphism as smooth of given relative dimension.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_isStandardSmoothOfRelativeDimension_appLE_fiberToSpecResidueField.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.exists_isStandardSmoothOfRelativeDimension_appLE_fiberToSpecResidueField
    {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) (m : ℕ)
    (U : Y.Opens) (hU : IsAffineOpen U) (V : X.Opens) (hV : IsAffineOpen V) (hxV : x ∈ V) (e : V ≤ f ⁻¹ᵁ U)
    (h : (f.appLE U V e).hom.IsStandardSmoothOfRelativeDimension m) :
    ∃ (U' : (Spec (Y.residueField (f.base x))).Opens) (V' : (f.fiber (f.base x)).Opens) (_ : IsAffineOpen V')
      (_ : f.asFiber x ∈ V') (e' : V' ≤ (f.fiberToSpecResidueField (f.base x)) ⁻¹ᵁ U'),
      ((f.fiberToSpecResidueField (f.base x)).appLE U' V' e').hom.IsStandardSmoothOfRelativeDimension m := by sorry
