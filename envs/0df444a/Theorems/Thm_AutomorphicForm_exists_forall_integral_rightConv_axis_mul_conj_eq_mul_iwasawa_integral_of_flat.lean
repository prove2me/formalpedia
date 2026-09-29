-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_integral_rightConv_axis_mul_conj_eq_mul_iwasawa_integral_of_flat
-- name    : AutomorphicForm.exists_forall_integral_rightConv_axis_mul_conj_eq_mul_iwasawa_integral_of_flat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/1d6a9b93-3a89-5da0-9666-1e3a2dbb7ab0
-- title:
--   Iwasawa unfolding of flat induced matrix coefficients
-- statement:
--   Let $K$ be a number field, write $G = \mathrm{GL}_2(\mathbb{A}_K)$ for `AdelicGL2 (𝓞 K) K`, and let $\alpha_m$ be the character of the idele group $(\mathbb{A}_K)^\times$ obtained from the module `distribHaarChar` of $\mathbb{A}_K$ by viewing its $\mathbb{R}_{\ge 0}$-values in $\mathbb{R}^\times$. The assertion is the existence of a real $c > 0$, depending only on $K$ (through the chosen Haar normalisations), such that the following holds for every proof that $\alpha_m$ takes positive values, all monoid homomorphisms $\mu, \nu : (\mathbb{A}_K)^\times \to \mathbb{C}^\times$ with continuous underlying $\mathbb{C}$-valued functions, every $w \in \mathbb{R}$, every continuous compactly supported $f_0 : G \to \mathbb{C}$, every pair of families $\varphi, \psi : \mathbb{C} \times G \to \mathbb{C}$ such that, for each $s$, $\varphi_s$ and $\psi_s$ satisfy `IsInducedSection` for the characters $\eta_1(s) = \mu\,\alpha_m^{\,s+1/2}$ and $\eta_2(s) = \nu\,\alpha_m^{-(s+1/2)}$, i.e. $\varphi_s(bg) = \eta_1(s)(\mathrm{diag}_1 b)\,\eta_2(s)(\mathrm{diag}_2 b)\,\varphi_s(g)$ for $b$ in the adelic Borel subgroup, both families being jointly continuous in $(s,g)$ and flat, meaning $\varphi_s(k) = \varphi_0(k)$ and $\psi_s(k) = \psi_0(k)$ for all $s$ and all $k$ in `adelicMaximalCompact K` (the elements whose finite part is integral and whose archimedean components are row isometries), and every $t \in \mathbb{R}$: the integral over $k \in \mathbf{K} =$ `adelicMaximalCompact K`, against `maximalCompactHaar K`, of $$\Big(\int_G \psi_{it}(kg)\,\|\det(kg)\|^{w/2} f_0(g)\,dg\Big)\,\overline{\varphi_{it}(k)}$$ equals $c$ times the iterated integral over $k \in \mathbf{K}$, $x \in \mathbb{A}_K$ (additive Haar), $u$ and $t'$ in $(\mathbb{A}_K)^\times$ (idelic Haar) and $k' \in \mathbf{K}$ of $$\eta_1(it)(ut')\,\eta_2(it)(u)\,\|\det(z(u)a(t'))\|^{w/2}\,\|t'\|^{-1}\,f_0\big(k^{-1} n(x) z(u) a(t') k'\big)\,\psi_0(k')\,\overline{\varphi_0(k)},$$ where $n(x)$ is the upper unipotent matrix, $z(u)$ the central scalar, $a(t') = \mathrm{diag}(t',1)$, $\|\cdot\|$ is the idele norm given by the module character, and the measures are ordered with $k'$ innermost and $k$ outermost.
--
--   This is the unfolding of the matrix coefficient of a right convolution operator against flat principal-series sections along the Iwasawa decomposition $G = N Z A_1 \mathbf{K}$ of $\mathrm{GL}_2(\mathbb{A}_K)$, evaluated at the unitary point $s = it$; it contains no estimate. It feeds the archimedean decay bound for such coefficients, [`AutomorphicForm.exists_forall_norm_rightConv_axis_pairing_add_norm_deriv_le_mul_rpow_neg_archParam_of_isUnitFactorization`](thm.html#AutomorphicForm.exists_forall_norm_rightConv_axis_pairing_add_norm_deriv_le_mul_rpow_neg_archParam_of_isUnitFactorization), whose binders it shares.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_integral_rightConv_axis_mul_conj_eq_mul_iwasawa_integral_of_flat.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
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
import Definitions.Def_NumberField_IdeleProductMeasure

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox
open NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal Classical

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.exists_forall_integral_rightConv_axis_mul_conj_eq_mul_iwasawa_integral_of_flat
    (K : Type) [Field K] [NumberField K]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ] :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    letI := adeleBorel (𝓞 K) K
    ∃ c : ℝ, 0 < c ∧
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
      (_hμc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μ z : ℂˣ) : ℂ))
      (_hνc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν z : ℂˣ) : ℂ))
      (w : ℝ)
      (f₀ : AdelicGL2 (𝓞 K) K → ℂ) (_hf₀ : Continuous f₀) (_hf₀c : HasCompactSupport f₀)
      (φf ψf : ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hφf : ∀ s, IsInducedSection (𝓞 K) K (etaFst μ αm hαm s) (etaSnd ν αm hαm s) (φf s))
      (_hψf : ∀ s, IsInducedSection (𝓞 K) K (etaFst μ αm hαm s) (etaSnd ν αm hαm s) (ψf s))
      (_hφfjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => φf p.1 p.2))
      (_hψfjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => ψf p.1 p.2))
      (_hφfflat : ∀ (s : ℂ) (k : adelicMaximalCompact K),
        φf s (k : AdelicGL2 (𝓞 K) K) = φf 0 (k : AdelicGL2 (𝓞 K) K))
      (_hψfflat : ∀ (s : ℂ) (k : adelicMaximalCompact K),
        ψf s (k : AdelicGL2 (𝓞 K) K) = ψf 0 (k : AdelicGL2 (𝓞 K) K))
      (t : ℝ),
    (∫ k, rightConv K (fun g : AdelicGL2 (𝓞 K) K => ψf ((t : ℂ) * Complex.I) g *
          (((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g)) ^ (w / 2) : ℝ) : ℂ)) f₀ (k : AdelicGL2 (𝓞 K) K) *
        conj (φf ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K))
      = (c : ℂ) * ∫ k, ∫ x, ∫ u, ∫ t', ∫ k',
          ((etaFst μ αm hαm ((t : ℂ) * Complex.I) (u * t') : ℂˣ) : ℂ) *
          ((etaSnd ν αm hαm ((t : ℂ) * Complex.I) u : ℂˣ) : ℂ) *
          (((NumberField.TateGlobal.ideleNorm K
              (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K u * diagOne t'))) ^ (w / 2) : ℝ) : ℂ) *
          (((NumberField.TateGlobal.ideleNorm K t')⁻¹ : ℝ) : ℂ) *
          f₀ ((k : AdelicGL2 (𝓞 K) K)⁻¹ *
              (unipotentGL2 x * centralScalar (𝓞 K) K u * diagOne t' * (k' : AdelicGL2 (𝓞 K) K))) *
          ψf 0 (k' : AdelicGL2 (𝓞 K) K) * conj (φf 0 (k : AdelicGL2 (𝓞 K) K))
        ∂(maximalCompactHaar K) ∂(NumberField.Idele.idelicHaar K) ∂(NumberField.Idele.idelicHaar K)
        ∂(adelicAddHaar (𝓞 K) K) ∂(maximalCompactHaar K) := by sorry
