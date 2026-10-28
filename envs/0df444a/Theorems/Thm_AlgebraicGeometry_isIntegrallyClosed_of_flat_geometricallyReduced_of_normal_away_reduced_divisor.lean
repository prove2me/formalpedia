-- Prove2me | Theorems.Thm_AlgebraicGeometry_isIntegrallyClosed_of_flat_geometricallyReduced_of_normal_away_reduced_divisor
-- name    : AlgebraicGeometry.isIntegrallyClosed_of_flat_geometricallyReduced_of_normal_away_reduced_divisor
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-26T19:35:34.170431+00:00
-- url     : https://prove2.me/theorems/5225a3f6-41f5-4a7f-b44e-916046696503
-- title:
--   Normality of a flat geometrically reduced family across a reduced principal base boundary
-- statement:
--   Let $R$ be a noetherian commutative ring and let $A$ be an integral domain that is a flat $R$-algebra. Suppose the actual morphism
--   $$\operatorname{Spec}A\longrightarrow\operatorname{Spec}R$$
--   has geometrically reduced fibres. Let $t\in R$, write $a$ for its image in $A$, and suppose that $a\ne0$, the ring $R/(t)$ is reduced, and $A[1/a]$ is integrally closed.
--
--   Then $A$ is integrally closed, and every local ring of the actual scheme $\operatorname{Spec}A$ is integrally closed. In particular, the whole affine total space is normal, including its points above the principal closed subscheme $V(t)$ of the base.
--
--   The base need not be a domain or normal; properness, smoothness and a finite-type hypothesis on the family are unnecessary. The theorem is a normality step once a reduced Cartier boundary has been supplied. It does not construct that boundary, a stable family, or a smooth alteration.
-- source:
--   Derived normality criterion for the boundary-family stage of A. J. de Jong, Smoothness, semi-stability and alterations, Publications Mathématiques de l’IHÉS 83 (1996), Sections 3.1-3.3, pp. 62-63, and Section 4.21, p. 74; https://www.numdam.org/item/PMIHES_1996__83__51_0.pdf . The displayed statement is an auxiliary affine criterion, not a verbatim numbered theorem. Reducedness of the actual base change is Mathlib GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian, https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/AlgebraicGeometry/Geometrically/Reduced.lean . Integral closedness uses the Proved principal-quotient criterion https://prove2.me/theorems/4f59eb2d-5956-5ea7-bc0d-e782eab822b4 and localization criterion https://prove2.me/theorems/631599f7-7ca6-5589-906b-ddcff44f67e7 . Normality is local as in Stacks Project, Section 10.37, https://stacks.math.columbia.edu/tag/037B . This does not assert a smooth total space or the existence of a reduced Cartier boundary.

import Mathlib
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory
universe u

theorem AlgebraicGeometry.isIntegrallyClosed_of_flat_geometricallyReduced_of_normal_away_reduced_divisor
    (R A : Type u) [CommRing R] [IsNoetherianRing R] [CommRing A] [IsDomain A]
    [Algebra R A] [Module.Flat R A]
    [GeometricallyReduced (Spec.map (CommRingCat.ofHom (algebraMap R A)))]
    (t : R) (ht : algebraMap R A t ≠ 0)
    [_root_.IsReduced (R ⧸ Ideal.span {t})]
    [IsIntegrallyClosed (Localization.Away (algebraMap R A t))] :
    IsIntegrallyClosed A ∧
      ∀ x : Spec (.of A), IsIntegrallyClosed ((Spec (.of A)).presheaf.stalk x) := by sorry
