-- Prove2me | Theorems.Thm_AutomorphicForm_hasSum_whittakerCoefficient_one_diagOne_principalIdeles_unipotentAverage
-- name    : AutomorphicForm.hasSum_whittakerCoefficient_one_diagOne_principalIdeles_unipotentAverage
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/3db572c1-b6e8-53c2-93d9-732aee1b81d8
-- title:
--   Torus Whittaker expansion of a smoothed adelic cusp form
-- statement:
--   Let $F$ be a number field, let $c,u,d_1,d_2$ be reals with $d_1<d_2$, and let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_F)$; write $D=\bigcup_{x\in T}\,(\,\cdot\,x)\,[\,\mathrm{centreCutSiegelSet}\ F\ c\ u\ d_1\ d_2\,]$ for the union of the right translates by the elements of $T$ of the set of $g$ whose finite part lies in $\mathrm{finiteIntegralGL2}$ and which satisfy, at every infinite place $w$, $c\le \mathrm{localHeight}$, $\mathrm{xWindowSq}\le u^2$ and $\mathrm{archDetNorm}_w(g)\in[d_1,d_2]$. Assume $D$ covers $\mathrm{GL}_2(\mathbb{A}_F)$ modulo left multiplication by $\mathrm{GL}_2(F)$ and right multiplication by central ideles. Let $\mathrm{pins}$ be the production pins attached to $D$, to the levels $N\mapsto \mathrm{levelOne}\ N\sqcap\ker(\mathrm{glArch})$, to the Hecke generators $v\mapsto \mathrm{heckeGen}\ v$ and to the box $\mathrm{adelicBox}\ F$; thus the measure on $\mathrm{GL}_2(\mathbb{A}_F)$ is Haar, the central subgroup is all of $\mathbb{A}_F^\times$, and the additive measure $\nu$ is adelic additive Haar conditioned to $\mathrm{adelicBox}\ F$. Let $\xi$ be a character of that central subgroup, and let $\varphi:\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ be continuous and satisfy `IsCuspAutomorphicFnAt` for these pins and $\xi$, i.e. the `LsXiMemberAt` condition for the pins data together with the vanishing, at every $g$, of the constant term of $\varphi$ along $x\mapsto\mathrm{unipotentGL2}(x)$ taken with respect to $\nu$. Let $f$ be a factorizable test function, that is $f(g)=f_\infty(\mathrm{glArch}\,g)\,f_{\mathrm{fin}}(\mathrm{glFin}\,g)$ with $f_\infty$ of compact support and given by a smooth function of the archimedean matrix entries, and $f_{\mathrm{fin}}$ locally constant of compact support. Let $B$ lie in the Schwartz–Bruhat space of $\mathbb{A}_F$ and let $\Phi$ satisfy $\Phi(h)=\int_{\mathbb{A}_F} B(x)\,(\varphi * f)(h\,\mathrm{unipotentGL2}(x))\,dx$ for all $h$, where $(\varphi*f)(g)=\int_{\mathrm{GL}_2(\mathbb{A}_F)}\varphi(gy)f(y)\,dy$. Let $\psi$ be an additive character of $\mathbb{A}_F$ that is trivial on $F$, continuous and non-trivial, and let $a\in\mathbb{A}_F^\times$. Then the family indexed by the principal ideles $\gamma\in F^\times\subset\mathbb{A}_F^\times$ of the first Whittaker coefficients $\int \Phi(\mathrm{unipotentGL2}(x)\,\mathrm{diag}(\gamma a,1))\,\psi(-x)\,d\nu(x)$ is summable with sum $\Phi(\mathrm{diag}(a,1))$.
--
--   This is the Whittaker–Fourier expansion of a cusp form on $\mathrm{GL}_2$ over a number field, restricted to the diagonal torus $\mathrm{diag}(a,1)$ and applied to the Schwartz–Bruhat average $\Phi$ of the right convolution $\varphi * f$: the constant term drops out by cuspidality and the non-zero coefficients are transported to the first one by the principal idele $\gamma$. It feeds the analytic continuation of the associated zeta integral in [`AutomorphicForm.exists_differentiable_forall_integral_zetaIntegrand_whittakerCoefficient_unipotentAverage_eq`](thm.html#AutomorphicForm.exists_differentiable_forall_integral_zetaIntegrand_whittakerCoefficient_unipotentAverage_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_hasSum_whittakerCoefficient_one_diagOne_principalIdeles_unipotentAverage.lean

import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_BoundedGenuineCuspRealization
import Definitions.Def_UnramifiedWhittaker_ZetaIntegrand
import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_M4aHerbrand_IdeleClassVocab

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar MeasureTheory
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain NumberField.TateGlobal
open UnramifiedWhittaker
open scoped Classical

theorem AutomorphicForm.hasSum_whittakerCoefficient_one_diagOne_principalIdeles_unipotentAverage
    (F : Type) [Field F] [NumberField F]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (ξ : (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).Z →* ℂˣ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : IsCuspAutomorphicFnAt F
      (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ φ)
    (hcont : Continuous φ)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f)
    (B : AdeleRing (𝓞 F) F → ℂ) (hB : B ∈ NumberField.AdelicFourier.schwartzBruhat F)
    (Φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hΦ : ∀ h : AdelicGL2 (𝓞 F) F, Φ h = (letI := adeleBorel (𝓞 F) F
        ∫ x, B x * rightConv F φ f (h * unipotentGL2 x) ∂(adelicAddHaar (𝓞 F) F)))
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsGlobalAddChar F ψ)
    (a : (AdeleRing (𝓞 F) F)ˣ) :
    HasSum (fun γ : ↥(M4aHerbrand.principalIdeles (𝓞 F) F) =>
        whittakerCoefficient F
          (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ψ Φ 1 (diagOne ((γ : (AdeleRing (𝓞 F) F)ˣ) * a)))
      (Φ (diagOne a)) := by sorry
