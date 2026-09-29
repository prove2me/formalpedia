-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_flat_kaehlerDifferential_cover_of_smooth
-- name    : AlgebraicGeometry.Scheme.TwoAffineOpenCover.flat_kaehlerDifferential_cover_of_smooth
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/139523d8-3ba8-50cf-a905-fc5b7306ef32
-- title:
--   Flatness of Ω_{A_i/R} for a two-chart affine cover
-- statement:
--   Let $R$ be a commutative ring and $X$ a scheme, and let $\mathcal V$ be a `TwoAffineOpenCover` of $X$: data consisting of two opens $U_0, U_1 \subseteq X$, proofs that $U_0$, $U_1$ and $U_0 \cap U_1$ are affine opens, and a proof that $U_0 \sqcup U_1 = \top$. Let $c \colon X \to \operatorname{Spec} R$ be a morphism of schemes which is smooth (the Mathlib typeclass `Smooth`). Associated with $\mathcal V$ and $c$ is the two-chart Čech cover `𝒱.cover c`, whose three rings are $A_0 = \Gamma(X, U_0)$, $A_1 = \Gamma(X, U_1)$ and $A_{01} = \Gamma(X, U_0 \cap U_1)$, each made an $R$-algebra by the ring homomorphism obtained from the inverse of $\Gamma$–$\operatorname{Spec}$ adjunction isomorphism for $R$ followed by $c.appLE\ \top\ U\ \mathrm{le\_top}$, and whose two restriction maps $\rho_0, \rho_1$ are the $R$-algebra restriction maps into $A_{01}$. The conclusion is the conjunction of three statements: the modules of Kähler differentials $\Omega_{A_0/R}$, $\Omega_{A_1/R}$ and $\Omega_{A_{01}/R}$ are each flat as $R$-modules.
--
--   This supplies the flatness hypotheses on relative differentials needed when the Čech description of a two-chart affine cover of a smooth scheme over $R$ is used to compute $H^0$ of the sheaf of differentials and its behaviour under base change; it is invoked in the construction of free bases for $H^0(\Omega^1)$ of a smooth relative curve and, downstream, in the comparison of $q$-expansions on modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_flat_kaehlerDifferential_cover_of_smooth.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverKaehler

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.TwoAffineOpenCover.flat_kaehlerDifferential_cover_of_smooth
    {R : Type u} [CommRing R] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover)
    (c : X ⟶ Spec (.of R)) [Smooth c] :
    Module.Flat R Ω[(𝒱.cover c).A0⁄R] ∧ Module.Flat R Ω[(𝒱.cover c).A1⁄R] ∧
      Module.Flat R Ω[(𝒱.cover c).A01⁄R] := by sorry
