-- Prove2me | Theorems.Thm_AutomorphicForm_weylIntertwiningIntegral_convOp_eq_convOp_weylIntertwiningIntegral_of_isInducedSection_of_re_gt_half
-- name    : AutomorphicForm.weylIntertwiningIntegral_convOp_eq_convOp_weylIntertwiningIntegral_of_isInducedSection_of_re_gt_half
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/f126b44a-52c0-52d2-968d-84c7f8d935d3
-- title:
--   Right convolution commutes with the Weyl intertwining integral
-- statement:
--   Let $K$ be a number field, and let $\alpha_m$ be the monoid homomorphism $(\mathbb{A}_K)^\times \to \mathbb{R}^\times$ obtained from the distributive Haar character `distribHaarChar` of the adele ring $\mathbb{A}_K =$ `AdeleRing (𝓞 K) K` by composing with the inclusion $\mathbb{R}_{\ge 0} \to \mathbb{R}$ and passing to units; the adele ring carries its Borel $\sigma$-algebra, and the group $\mathrm{GL}_2(\mathbb{A}_K)$ its Borel $\sigma$-algebra as well. Assume $\alpha_m(x) > 0$ for all $x$. Let $\mu, \nu : (\mathbb{A}_K)^\times \to \mathbb{C}^\times$ be monoid homomorphisms which are unitary in the sense that $\lVert \mu(x)\rVert = \lVert \nu(x)\rVert = 1$ for all $x$, and let $s \in \mathbb{C}$ with $\operatorname{Re} s > 1/2$. Let $\varphi : \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$ be continuous and an induced section for the pair of characters $\eta_1 = \mu \cdot \alpha_m^{\,s+1/2}$ and $\eta_2 = \nu \cdot \alpha_m^{-(s+1/2)}$ (complex powers of the positive reals $\alpha_m(x)$), that is, $\varphi(bg) = \eta_1(b_{00})\,\eta_2(b_{11})\,\varphi(g)$ for every $g$ and every $b$ in the adelic Borel subgroup `adelicBorel`, $b_{00}$ and $b_{11}$ being the diagonal entries of $b$ viewed as units. Let $f : \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$ be continuous with compact support. Then for every $g \in \mathrm{GL}_2(\mathbb{A}_K)$ the two operations commute: applying `weylIntertwiningIntegral` with respect to the additive Haar measure `adelicAddHaar`, namely $u \mapsto \int_{\mathbb{A}_K} u\big(w^{-1}\,n(x)\,g\big)\,dx$ with $n(x) = \begin{pmatrix}1 & x\\ 0 & 1\end{pmatrix}$ and $w$ the adelic Weyl element, to `convOp K f φ` (the right convolution `rightConv K φ f`) gives the same value at $g$ as applying `convOp K f` to the function `weylIntertwiningIntegral (𝓞 K) K (adelicAddHaar (𝓞 K) K) φ`.
--
--   This is the commutation $M(s)R(f) = R(f)M(s)$ of right convolution by a compactly supported continuous function with the rank-one Weyl intertwining integral, inside the half-plane $\operatorname{Re} s > 1/2$ where the intertwining integral converges absolutely. It feeds the statements that identify the analytic continuation in $s$ of the convolved intertwining family with the convolution of the continued family, and thence the Bruhat-type expansions used in the Eisenstein part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_weylIntertwiningIntegral_convOp_eq_convOp_weylIntertwiningIntegral_of_isInducedSection_of_re_gt_half.lean

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

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.weylIntertwiningIntegral_convOp_eq_convOp_weylIntertwiningIntegral_of_isInducedSection_of_re_gt_half
    (K : Type) [Field K] [NumberField K] :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    letI := adeleBorel (𝓞 K) K
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 K) K μ) (_hν : IsUnitaryChar (𝓞 K) K ν)
      (s : ℂ) (_hs : (1 / 2 : ℝ) < s.re)
      (φ : AdelicGL2 (𝓞 K) K → ℂ)
      (_hφ : IsInducedSection (𝓞 K) K (etaFst μ αm hαm s) (etaSnd ν αm hαm s) φ)
      (_hφc : Continuous φ)
      (f : AdelicGL2 (𝓞 K) K → ℂ) (_hf : Continuous f) (_hfc : HasCompactSupport f),
    ∀ g : AdelicGL2 (𝓞 K) K,
      weylIntertwiningIntegral (𝓞 K) K (adelicAddHaar (𝓞 K) K) (convOp K f φ) g =
        convOp K f (weylIntertwiningIntegral (𝓞 K) K (adelicAddHaar (𝓞 K) K) φ) g := by sorry
