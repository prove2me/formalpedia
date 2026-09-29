-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_finite_H0_H1_kaehlerSections
-- name    : AlgebraicGeometry.Scheme.TwoAffineOpenCover.finite_H0_H1_kaehlerSections
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/505e9a09-cc39-5687-9b09-cfe500d3b1d6
-- title:
--   Finiteness of Čech H⁰ and H¹ of Ω¹ for proper morphisms
-- statement:
--   Let $R$ be a Noetherian commutative ring and $X$ a scheme, and let $\mathcal V$ be a two-chart affine open cover of $X$: a pair of opens $U_0, U_1 \subseteq X$, each affine, with affine intersection $U_0 \cap U_1$ and with $U_0 \sqcup U_1 = \top$. Let $c \colon X \to \operatorname{Spec} R$ be a proper morphism. Through $c$ the three section rings $A_0 = \Gamma(X, U_0)$, $A_1 = \Gamma(X, U_1)$ and $A_{01} = \Gamma(X, U_0 \cap U_1)$ become $R$-algebras, and the two restrictions $\rho_0 \colon A_0 \to A_{01}$, $\rho_1 \colon A_1 \to A_{01}$ are $R$-algebra maps. The associated sections object assigns the modules of Kähler differentials $\Omega_{A_0/R}$, $\Omega_{A_1/R}$, $\Omega_{A_{01}/R}$ together with the $R$-linear maps $r_0, r_1$ induced functorially by $\rho_0, \rho_1$, and its Čech differential is the $R$-linear map $\Omega_{A_0/R} \times \Omega_{A_1/R} \to \Omega_{A_{01}/R}$, $(m_0, m_1) \mapsto r_1(m_1) - r_0(m_0)$. The conclusion is that both its kernel, $H^0$, and the quotient of $\Omega_{A_{01}/R}$ by its range, $H^1$, are finite (i.e. finitely generated) $R$-modules.
--
--   This is the Čech-complex form, for a cover by two affine charts, of the coherence of higher direct images under a proper morphism over a Noetherian base, applied to the sheaf of relative differentials $\Omega^1_{X/R}$; it is the $\Omega^1$ counterpart of the corresponding statement for the structure sheaf. It supplies the finiteness input for the comparison of $\check H^0(\Omega^1)$ with $\check H^1(\mathcal O)$, and its compatibility with base change, for schemes smooth of relative dimension one over $R$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_finite_H0_H1_kaehlerSections.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverKaehler

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.TwoAffineOpenCover.finite_H0_H1_kaehlerSections
    {R : Type u} [CommRing R] [IsNoetherianRing R] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover)
    (c : X ⟶ Spec (.of R)) [IsProper c] :
    Module.Finite R (𝒱.kaehlerSections c).H0 ∧ Module.Finite R (𝒱.kaehlerSections c).H1 := by sorry
