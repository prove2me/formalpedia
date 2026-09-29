-- Prove2me | Theorems.Thm_AutomorphicForm_integral_maximalCompactHaar_rightConv_mul_conj_eq_integral_mul_conj_rightConv_star_of_isInducedSection_axis
-- name    : AutomorphicForm.integral_maximalCompactHaar_rightConv_mul_conj_eq_integral_mul_conj_rightConv_star_of_isInducedSection_axis
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/1542abde-467b-5797-8ddb-a7a2a00f2655
-- title:
--   Adjointness of right convolution for the maximal compact pairing
-- statement:
--   Let $K$ be a number field, and let $\alpha$ denote the positive real character of $\mathbb{A}_K^\times$ obtained from the distributive Haar character of the adele ring (composed with $\mathbb{R}_{\ge 0}\to\mathbb{R}$ and viewed as a homomorphism into $\mathbb{R}^\times$), the adele ring carrying its Borel $\sigma$-algebra. Assume $\alpha(x)>0$ for all $x$. Let $\mu,\nu:\mathbb{A}_K^\times\to\mathbb{C}^\times$ be group homomorphisms with $|\mu(x)|=|\nu(x)|=1$ and $|\nu(x)|=1$ for all $x$, let $t\in\mathbb{R}$, and put $s=it$. Let $\Psi,\chi:\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ be continuous and both satisfy the induced-section identity for the pair $(\mu\cdot\alpha^{s+1/2},\,\nu\cdot\alpha^{-(s+1/2)})$: for every $b$ in the Borel subgroup (matrices with vanishing lower-left entry) and every $g$, $\Psi(bg)=\mu(b_{11})\alpha(b_{11})^{s+1/2}\,\nu(b_{22})\alpha(b_{22})^{-(s+1/2)}\Psi(g)$, and likewise for $\chi$. Let $f:\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ be continuous with compact support. Writing $R(f)\varphi(g)=\int \varphi(gx) f(x)\,dx$ for the right convolution against the adelic Haar measure on $\mathrm{GL}_2(\mathbb{A}_K)$, and integrating over the maximal compact subgroup (finite part integral, archimedean components row-isometries) with its Haar measure, the conclusion is $$\int_{\mathbf{K}} R(f)\Psi(k)\,\overline{\chi(k)}\,dk=\int_{\mathbf{K}} \Psi(k)\,\overline{R(f^{*})\chi(k)}\,dk,\qquad f^{*}(y)=\overline{f(y^{-1})}.$$
--
--   This is the statement that right convolution by $f$ and by $f^{*}(y)=\overline{f(y^{-1})}$ are adjoint for the pairing over the maximal compact subgroup of $\mathrm{GL}_2(\mathbb{A}_K)$, on continuous sections of the induced representation attached to unitary characters $\mu,\nu$ at the unitary-axis parameter $s=it$. It feeds the expansion of such pairings in terms of an orthonormal family of sections.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_integral_maximalCompactHaar_rightConv_mul_conj_eq_integral_mul_conj_rightConv_star_of_isInducedSection_axis.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_GeometricRemainder
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_AutomorphicFnAt
import Definitions.Def_AutomorphicForm_ResidualSpan

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox
open NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.integral_maximalCompactHaar_rightConv_mul_conj_eq_integral_mul_conj_rightConv_star_of_isInducedSection_axis
    (K : Type) [Field K] [NumberField K] :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    letI := adeleBorel (𝓞 K) K
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 K) K μ) (_hν : IsUnitaryChar (𝓞 K) K ν)
      (t : ℝ) (Ψ χ : AdelicGL2 (𝓞 K) K → ℂ)
      (_hΨ : IsInducedSection (𝓞 K) K (etaFst μ αm hαm ((t : ℂ) * Complex.I)) (etaSnd ν αm hαm ((t : ℂ) * Complex.I)) Ψ)
      (_hχ : IsInducedSection (𝓞 K) K (etaFst μ αm hαm ((t : ℂ) * Complex.I)) (etaSnd ν αm hαm ((t : ℂ) * Complex.I)) χ)
      (_hΨc : Continuous Ψ) (_hχc : Continuous χ)
      (f : AdelicGL2 (𝓞 K) K → ℂ) (_hf : Continuous f) (_hfc : HasCompactSupport f),
    ∫ k, rightConv K Ψ f (k : AdelicGL2 (𝓞 K) K) * conj (χ (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) =
      ∫ k, Ψ (k : AdelicGL2 (𝓞 K) K) * conj (rightConv K χ (fun y => conj (f y⁻¹)) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) := by sorry
