-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_ringEquiv_stalk_localRing_coe_eq
-- name    : AlgebraicGeometry.exists_ringEquiv_stalk_localRing_coe_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/38e325c3-4913-5ad8-9f19-73b13032052d
-- title:
--   Stalk of an integral scheme as a subring of F
-- statement:
--   Let $X$ be an integral scheme (in the lowest universe) and let $F$ be a field together with a ring isomorphism $\varphi : F \xrightarrow{\sim} K(X)$ onto the function field of $X$, and let $x$ be a point of $X$. The assertion is that there exists a ring isomorphism $e$ from the stalk $\mathcal{O}_{X,x} =$ `X.presheaf.stalk x` onto the subring `SemistableModel.localRing X φ x` of $F$, which by definition is the range of the ring homomorphism $\varphi^{-1} \circ (\text{algebraMap} : \mathcal{O}_{X,x} \to K(X))$, such that $e$ is induced by that very homomorphism: for every $z \in \mathcal{O}_{X,x}$, the element $e(z)$, viewed through the inclusion of the subring into $F$, equals $\varphi^{-1}$ applied to the image of $z$ under the canonical map $\mathcal{O}_{X,x} \to K(X)$. Thus the conclusion both produces the isomorphism and pins it down by an explicit formula, so that any further compatibility of $e$ (with constants mapped in from a base ring, or with specialisation maps between stalks) is a matter of unfolding this formula.
--
--   This is the standard fact that, on an integral scheme, each local ring maps injectively into the function field, so that it may be identified with its image there; the identification is recorded in the form needed to read stalks of a model as concrete subrings of a fixed field $F$. It is used in the analysis of the modular curve of full level at a point, where completed local rings of a global model are compared with those of an affine chart inside $F$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_ringEquiv_stalk_localRing_coe_eq.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry IsLocalRing AlgebraicCurve

theorem AlgebraicGeometry.exists_ringEquiv_stalk_localRing_coe_eq
    (X : Scheme.{0}) [IsIntegral X] {F : Type} [Field F] (φ : F ≃+* X.functionField) (x : X) :
    ∃ e : X.presheaf.stalk x ≃+* ↥(SemistableModel.localRing X φ x),
      ∀ z : X.presheaf.stalk x,
        ((e z : ↥(SemistableModel.localRing X φ x)) : F) = φ.symm (algebraMap (X.presheaf.stalk x) X.functionField z) := by sorry
