-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_eq_smul_kaehlerH0_and_val_eq_of_val_eq_smul
-- name    : AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_eq_smul_kaehlerH0_and_val_eq_of_val_eq_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/108fdb57-126b-5642-8b63-64d81c11c24a
-- title:
--   Dividing a Čech 0-cocycle of Kähler differentials by varpi
-- statement:
--   Let $R$ be a commutative domain and $\varpi \in R$ a non-zero element, let $X$ be a scheme equipped with a morphism $c \colon X \to \operatorname{Spec} R$, and let $\mathcal V$ be a two-affine open cover of $X$, that is, a pair of opens $U_0, U_1$ which are affine, have affine intersection, and satisfy $U_0 \sqcup U_1 = \top$. Write $A_0 = \Gamma(X, U_0)$, $A_1 = \Gamma(X, U_1)$, $A_{01} = \Gamma(X, U_0 \sqcap U_1)$, each an $R$-algebra via $c$, and assume the module of Kähler differentials $\Omega_{A_{01}/R}$ is flat over $R$. The associated $0$-cocycle module is the $R$-submodule of $\Omega_{A_0/R} \times \Omega_{A_1/R}$ given by the kernel of $(m_0, m_1) \mapsto -r_0(m_0) + r_1(m_1)$, where $r_0, r_1$ are the restriction maps on differentials induced by $A_0 \to A_{01}$ and $A_1 \to A_{01}$. Let $\omega$ be an element of this kernel and let $\omega_0 \in \Omega_{A_0/R}$, $\omega_1 \in \Omega_{A_1/R}$ be such that the two components of $\omega$ equal $\varpi \cdot \omega_0$ and $\varpi \cdot \omega_1$ respectively. Then there exists $\omega'$ in the same kernel with $\omega = \varpi \cdot \omega'$ and with underlying pair exactly $(\omega_0, \omega_1)$.
--
--   This is the statement that the module of Čech $0$-cocycles for a two-chart cover is saturated with respect to a non-zero scalar, provided the module of differentials on the overlap is flat (hence torsion-free) over the base domain: a pair of chartwise quotients by $\varpi$ of a cocycle is again a cocycle. It is the final step of [`AlgebraicGeometry.exists_eq_smul_kaehlerH0_of_germ_eq_smul_of_isIntegral_fibre_of_smoothOfRelativeDimension_one`](thm.html#AlgebraicGeometry.exists_eq_smul_kaehlerH0_of_germ_eq_smul_of_isIntegral_fibre_of_smoothOfRelativeDimension_one), where global $1$-forms on an integral model are divided by a uniformiser.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_eq_smul_kaehlerH0_and_val_eq_of_val_eq_smul.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverKaehler

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

theorem AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_eq_smul_kaehlerH0_and_val_eq_of_val_eq_smul
    {R : Type u} [CommRing R] [IsDomain R] (ϖ : R) (hϖ : ϖ ≠ 0)
    {X : Scheme.{u}} (c : X ⟶ Spec (.of R)) (𝒱 : X.TwoAffineOpenCover)
    [Module.Flat R Ω[(𝒱.cover c).A01⁄R]]
    (ω : ↥((𝒱.kaehlerSections c).H0)) (ω₀ : Ω[(𝒱.cover c).A0⁄R]) (ω₁ : Ω[(𝒱.cover c).A1⁄R])
    (h0 : ω.val.1 = ϖ • ω₀) (h1 : ω.val.2 = ϖ • ω₁) :
    ∃ ω' : ↥((𝒱.kaehlerSections c).H0), ω = ϖ • ω' ∧ ω'.val = (ω₀, ω₁) := by sorry
