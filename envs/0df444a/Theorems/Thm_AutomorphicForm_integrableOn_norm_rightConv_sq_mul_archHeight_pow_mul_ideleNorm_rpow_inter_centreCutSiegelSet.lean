-- Prove2me | Theorems.Thm_AutomorphicForm_integrableOn_norm_rightConv_sq_mul_archHeight_pow_mul_ideleNorm_rpow_inter_centreCutSiegelSet
-- name    : AutomorphicForm.integrableOn_norm_rightConv_sq_mul_archHeight_pow_mul_ideleNorm_rpow_inter_centreCutSiegelSet
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/a4de27d2-dffd-5910-83fd-e5f9bbaeeba2
-- title:
--   Integrability of ‖φ*f‖² against height powers on Siegel pieces
-- statement:
--   Let $K$ be a number field and let $c,u,d_1,d_2$ be reals with $d_1<d_2$, and $T$ a finite subset of $\mathrm{GL}_2(\mathbb{A}_K)$. Write $W=\bigcup_{x\in T}\,\mathfrak S\,x$, where $\mathfrak S=$ `centreCutSiegelSet K c u d₁ d₂` is the set of $g$ whose finite part lies in the integral subgroup `finiteIntegralGL2`, whose archimedean component satisfies $\mathrm{localHeight}\ge c$ and $\mathrm{xWindowSq}\le u^2$ at every infinite place, and with $\mathrm{archDetNorm}_w(g)\in[d_1,d_2]$ for all $w$; assume $W$ covers $\mathrm{GL}_2(\mathbb{A}_K)$ modulo left translation by $\mathrm{GL}_2(K)$ and right translation by adelic central scalars. Let $\chi$ be a character of the group $Z=\top$ of the pin data `productionPinsOf` attached to $W$, to the level subgroups $N\mapsto \mathrm{levelOne}(N)\sqcap\ker(\mathrm{glArch})$, to the Hecke generators $v\mapsto \mathrm{heckeGen}(v)$ and to the adelic box (these pins carry the Borel structure, the $\mathrm{GL}_2$-adelic Haar measure, and the additive adelic Haar measure conditioned to the box). Let $\varphi:\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ be continuous and satisfy `IsCuspAutomorphicFnAt` for these pins and $\chi$, i.e. $\varphi$ is an `LsXiMemberAt` member for that data and all its constant terms along `unipotentGL2` against the conditioned measure vanish. Let $f$ be a factorizable test function, $f(g)=f_\infty(\mathrm{glArch}\,g)\,f_{\mathrm{fin}}(\mathrm{glFin}\,g)$ with $f_\infty$ smooth in the mixed-space matrix entries and compactly supported and $f_{\mathrm{fin}}$ locally constant and compactly supported. Let $w\in\mathbb{R}$ and $0<e_1<e_2$, and let $\mathcal F$ be a measurable set contained in the slab $\{g:\ \|\det g\|_{\mathbb{A}}\in[e_1,e_2]\}$ which is a fundamental domain for the image of $\mathrm{GL}_2(K)$ with respect to the adelic Haar measure restricted to that slab. Finally let $c',u',d_1',d_2'$ be reals with $c'>0$ and $d_1'>0$, let $t\in\mathrm{GL}_2(\mathbb{A}_K)$ and $N\in\mathbb{N}$. Then the function $$g\mapsto \|(\varphi*f)(g)\|^2\,\bigl(1+\mathrm{archHeight}(\mathrm{glArch}(gt^{-1}))\bigr)^N\,\|\det g\|_{\mathbb{A}}^{-w},$$ where $(\varphi*f)(g)=\int \varphi(gx)f(x)\,dx$ and $\mathrm{archHeight}$ is the product over infinite places of $\mathrm{localHeight}$ raised to the multiplicity, is integrable on $\mathcal F\cap \mathfrak S(c',u',d_1',d_2')\,t$ with respect to the $\mathrm{GL}_2$-adelic Haar measure.
--
--   This is the domination estimate for the Rankin–Selberg slab integral: on a centre-cut Siegel piece the smoothed cusp form $\varphi*f$ decays faster than any power of the height, while the piece itself has finite Haar measure inside the slab of bounded idele determinant norm. It is invoked when establishing analyticity in the spectral parameter of the slab integrals attached to test data, and in the construction of right-convolution realisations of cusp constituents.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_integrableOn_norm_rightConv_sq_mul_archHeight_pow_mul_ideleNorm_rpow_inter_centreCutSiegelSet.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_WindowedSiegelSet
import Definitions.Def_NumberField_TateGlobalZeta
import Mathlib.MeasureTheory.Group.FundamentalDomain

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox NumberField.TateGlobal
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem AutomorphicForm.integrableOn_norm_rightConv_sq_mul_archHeight_pow_mul_ideleNorm_rpow_inter_centreCutSiegelSet
    (K : Type) [Field K] [NumberField K]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (χ : (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)).Z →* ℂˣ)
    (φ : AdelicGL2 (𝓞 K) K → ℂ)
    (hφ : IsCuspAutomorphicFnAt K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) χ φ)
    (hcont : Continuous φ)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : IsFactorizableTestFn K f)
    (w e₁ e₂ : ℝ) (he₁ : 0 < e₁) (he : e₁ < e₂)
    (𝓕 : Set (AdelicGL2 (𝓞 K) K)) (h𝓕m : MeasurableSet 𝓕)
    (h𝓕s : 𝓕 ⊆ {g | ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂})
    (h𝓕 : IsFundamentalDomain (globalPoints (𝓞 K) K).range 𝓕
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂}))
    (c' u' d₁' d₂' : ℝ) (hc' : 0 < c') (hd₁' : 0 < d₁') (t : AdelicGL2 (𝓞 K) K) (N : ℕ) :
    IntegrableOn
      (fun g => ‖rightConv K φ f g‖ ^ 2 *
        (1 + archHeight K (glArch (𝓞 K) K (g * t⁻¹))) ^ N *
        ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ (-w))
      (𝓕 ∩ (· * t) '' centreCutSiegelSet K c' u' d₁' d₂') (adelicGLHaar (Fin 2) (𝓞 K) K) := by sorry
