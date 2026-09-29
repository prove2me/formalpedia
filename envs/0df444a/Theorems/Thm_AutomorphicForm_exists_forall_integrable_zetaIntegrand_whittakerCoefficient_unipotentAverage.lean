-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_integrable_zetaIntegrand_whittakerCoefficient_unipotentAverage
-- name    : AutomorphicForm.exists_forall_integrable_zetaIntegrand_whittakerCoefficient_unipotentAverage
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/f84ffa86-93c5-5a96-b3f7-d268524f60a6
-- title:
--   Half-plane convergence of the GL(2) Whittaker zeta integral
-- statement:
--   Let $F$ be a number field, let $c,u,d_1,d_2$ be reals with $d_1<d_2$, and let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_F)$. Write $D=\bigcup_{x\in T}(\cdot\,x)\,[\,\mathrm{centreCutSiegelSet}\;F\;c\;u\;d_1\;d_2\,]$, the union of the right translates by elements of $T$ of the set of $g$ whose finite part lies in the integral subgroup `finiteIntegralGL2`, whose archimedean component at every infinite place $w$ has local height $\ge c$, window $\mathrm{xWindowSq}\le u^2$, and determinant norm $\mathrm{archDetNorm}_w(g)\in[d_1,d_2]$; assume `CoversModCentre`, i.e. every $g\in\mathrm{GL}_2(\mathbb{A}_F)$ can be written with $\gamma g z\in D$ for some $\gamma\in\mathrm{GL}_2(F)$ and some central idele scalar $z$. Fix the carrier data `productionPinsOf` attached to $D$, the levels $N\mapsto\mathrm{levelOne}(N)\sqcap$ `finiteAdelicGL2Subgroup` and the Hecke elements $v\mapsto\mathrm{heckeGen}(v)$, with box the adelic box $\mathrm{adelicBox}\,F$; here the measure on $\mathrm{GL}_2(\mathbb{A}_F)$ is Borel Haar, the subgroup $Z$ of central characters is all of $\mathbb{A}_F^\times$, and the measure on $\mathbb{A}_F$ is additive Haar conditioned on the box. Let $\xi:Z\to\mathbb{C}^\times$ be a character and $\varphi:\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ continuous and `IsCuspAutomorphicFnAt` for these data and $\xi$, that is, $\varphi$ satisfies the membership predicate `LsXiMemberAt` and its constant term $\int\varphi(u(x)\,g)$ along $x\mapsto\mathrm{unipotentGL2}(x)$ vanishes for all $g$. Let $f$ be a factorizable test function, a product of a compactly supported smooth function of the archimedean matrix entries with a locally constant compactly supported function of the finite part, and let $B$ lie in the Schwartz–Bruhat space of $\mathbb{A}_F$. Let $\Phi$ satisfy $\Phi(h)=\int_{\mathbb{A}_F}B(x)\,(\varphi*f)(h\,\mathrm{unipotentGL2}(x))\,dx$ for all $h$, where $(\varphi*f)(g)=\int\varphi(gy)f(y)\,dy$ over $\mathrm{GL}_2(\mathbb{A}_F)$. Let $\psi$ be a global additive character of $\mathbb{A}_F$ (trivial on $F$, continuous, nontrivial), let $\chi:\mathbb{A}_F^\times\to\mathbb{C}^\times$ be a continuous character trivial on principal ideles (not assumed unitary), and let $\nu$ be a Haar measure on $\mathbb{A}_F^\times$ with its Borel structure. Then there exists $\sigma_1\in\mathbb{R}$ such that for every $s\in\mathbb{C}$ with $\operatorname{Re}s>\sigma_1$ the function $a\mapsto W(\mathrm{diag}(a,1))\,\chi(a)\,\|a\|^{s-1}$ is $\nu$-integrable, where $W(g)=\int_{\mathbb{A}_F}\Phi(\mathrm{unipotentGL2}(x)\,g)\,\psi(-x)$ with respect to the conditioned measure on the box, and $\|a\|$ is the idele norm given by the distributive Haar character.
--
--   This is the absolute convergence statement for the $\mathrm{GL}_2$ Whittaker (Jacquet–Langlands) zeta integral attached to the first Fourier coefficient of a unipotent Schwartz–Bruhat average of a smoothed cusp form: the integrand is integrable against Haar measure on the idele class group in a right half-plane. It feeds the assembly of the zeta integral as a holomorphic function of $s$ in [`AutomorphicForm.exists_differentiable_forall_integral_zetaIntegrand_whittakerCoefficient_unipotentAverage_eq`](thm.html#AutomorphicForm.exists_differentiable_forall_integral_zetaIntegrand_whittakerCoefficient_unipotentAverage_eq), the convergence being obtained from finite-place support control for $W$ together with uniform archimedean decay estimates with polynomial loss in the idele norm.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_integrable_zetaIntegrand_whittakerCoefficient_unipotentAverage.lean

import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_BoundedGenuineCuspRealization
import Definitions.Def_UnramifiedWhittaker_ZetaIntegrand
import Definitions.Def_NumberField_AdelicFourier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar MeasureTheory
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain NumberField.TateGlobal
open UnramifiedWhittaker

theorem AutomorphicForm.exists_forall_integrable_zetaIntegrand_whittakerCoefficient_unipotentAverage
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
    (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hχ : IsIdeleClassChar (𝓞 F) F χ) (hχc : Continuous χ)
    [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
    (ν : Measure (AdeleRing (𝓞 F) F)ˣ) [ν.IsHaarMeasure] :
    ∃ σ₁ : ℝ, ∀ s : ℂ, σ₁ < s.re →
      Integrable (zetaIntegrand
        (fun g => whittakerCoefficient F
          (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ψ Φ 1 g) χ s) ν := by sorry
