-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_eq_smul_chart_of_eq_smul_chart_of_mem_kaehlerH0_of_isIntegral_fibre_of_smoothOfRelativeDimension_one
-- name    : AlgebraicGeometry.exists_eq_smul_chart_of_eq_smul_chart_of_mem_kaehlerH0_of_isIntegral_fibre_of_smoothOfRelativeDimension_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/4bb16c8f-e6e9-5191-9535-767e7bb7b040
-- title:
--   Divisibility of a Čech 1-form by varpi transfers between charts
-- statement:
--   Let $R$ be a commutative domain, $\varpi \in R$ a non-zero element such that the ideal $(\varpi)$ is maximal, and $q \colon R \to \kappa$ a ring homomorphism into a field with $\ker q = (\varpi)$. Let $X$ be a scheme, $c \colon X \to \operatorname{Spec} R$ a morphism that is smooth of relative dimension $1$, and $\mathcal{V}$ a two-affine open cover of $X$, that is, a pair of affine opens $U_0, U_1$ with $U_0 \sqcup U_1 = \top$ and $U_0 \sqcap U_1$ affine; assume the fibre product of $c$ with $\operatorname{Spec}$ of $q$ is an integral scheme. Write $A_0 = \Gamma(X, U_0)$, $A_1 = \Gamma(X, U_1)$, $A_{01} = \Gamma(X, U_0 \sqcap U_1)$, each an $R$-algebra via $c$, with restriction maps $\rho_0, \rho_1$ into $A_{01}$. Let $\omega = (\omega_0, \omega_1) \in \Omega_{A_0/R} \times \Omega_{A_1/R}$ lie in the kernel of the Čech differential $(\omega_0,\omega_1) \mapsto -r_0(\omega_0) + r_1(\omega_1)$, where $r_0, r_1$ are the maps on Kähler differentials induced by $\rho_0, \rho_1$ over the identity of $R$. Then two implications hold. First: if some point $x \in U_0$ lies in the image of the first projection $\operatorname{pullback}(c, \operatorname{Spec} q) \to X$, then $\omega_0 \in \varpi \, \Omega_{A_0/R}$ implies $\omega_1 \in \varpi \, \Omega_{A_1/R}$. Second, symmetrically: if some point $x \in U_1$ lies in that image, then $\omega_1 \in \varpi\, \Omega_{A_1/R}$ implies $\omega_0 \in \varpi\, \Omega_{A_0/R}$.
--
--   This is the transfer step for divisibility of a relative $1$-form on a smooth relative curve with integral special fibre: divisibility by the uniformiser on one chart propagates to the other chart, provided the first chart meets the special fibre (a necessary restriction, as $X = \mathbf{A}^1_R$ with $U_1 = X$, $U_0 = X[1/\varpi]$ and $\omega = dT$ shows). It is used in the proof of [`AlgebraicGeometry.exists_eq_smul_kaehlerH0_of_germ_eq_smul_of_isIntegral_fibre_of_smoothOfRelativeDimension_one`](thm.html#AlgebraicGeometry.exists_eq_smul_kaehlerH0_of_germ_eq_smul_of_isIntegral_fibre_of_smoothOfRelativeDimension_one), where divisibility known at a single germ is upgraded to divisibility of the whole Čech cocycle.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_eq_smul_chart_of_eq_smul_chart_of_mem_kaehlerH0_of_isIntegral_fibre_of_smoothOfRelativeDimension_one.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverKaehler

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

theorem AlgebraicGeometry.exists_eq_smul_chart_of_eq_smul_chart_of_mem_kaehlerH0_of_isIntegral_fibre_of_smoothOfRelativeDimension_one
    {R : Type u} [CommRing R] [IsDomain R] (ϖ : R) (hϖ : ϖ ≠ 0)
    (hmax : (Ideal.span {ϖ} : Ideal R).IsMaximal)
    {κ : Type u} [Field κ] (q : R →+* κ) (hker : RingHom.ker q = Ideal.span {ϖ})
    {X : Scheme.{u}} (c : X ⟶ Spec (.of R)) [SmoothOfRelativeDimension 1 c] (𝒱 : X.TwoAffineOpenCover)
    [IsIntegral (Limits.pullback c (Spec.map (CommRingCat.ofHom q)))]
    (ω : ↥((𝒱.kaehlerSections c).H0)) :
    (∀ x : X, x ∈ 𝒱.U0 → x ∈ Set.range (Limits.pullback.fst c (Spec.map (CommRingCat.ofHom q))).base →
        (∃ ω₀ : Ω[(𝒱.cover c).A0⁄R], ω.val.1 = ϖ • ω₀) → ∃ ω₁ : Ω[(𝒱.cover c).A1⁄R], ω.val.2 = ϖ • ω₁) ∧
    (∀ x : X, x ∈ 𝒱.U1 → x ∈ Set.range (Limits.pullback.fst c (Spec.map (CommRingCat.ofHom q))).base →
        (∃ ω₁ : Ω[(𝒱.cover c).A1⁄R], ω.val.2 = ϖ • ω₁) → ∃ ω₀ : Ω[(𝒱.cover c).A0⁄R], ω.val.1 = ϖ • ω₀) := by sorry
