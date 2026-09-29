-- Prove2me | Theorems.Thm_AutomorphicForm_exists_differentiable_forall_integral_zetaIntegrand_whittakerCoefficient_unipotentAverage_eq
-- name    : AutomorphicForm.exists_differentiable_forall_integral_zetaIntegrand_whittakerCoefficient_unipotentAverage_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/16d34cb9-4f26-5400-950b-d914df71cdba
-- title:
--   Entirety of the global Whittaker zeta integral on GL₂
-- statement:
--   Let $F$ be a number field, let $c,u,d_1,d_2$ be real numbers with $d_1<d_2$, and let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_F)$. Put $D=\bigcup_{x\in T}\{gx : g\in \mathrm{centreCutSiegelSet}\ F\ c\ u\ d_1\ d_2\}$, the Siegel set being those $g$ whose finite part is integral, all of whose archimedean components have local height $\ge c$, window $x$-coordinate squared $\le u^2$, and archimedean determinant norms in $[d_1,d_2]$; assume `CoversModCentre`, i.e. every $g\in\mathrm{GL}_2(\mathbb{A}_F)$ admits $\gamma\in\mathrm{GL}_2(F)$ and an idele unit $z$ with $\gamma g z\in D$. Let `pins` be `productionPinsOf` for $D$, the level subgroups $N\mapsto \mathrm{levelOne}\ N\sqcap$ `finiteAdelicGL2Subgroup`, the Hecke generators $v\mapsto$ `heckeGen`, and the box `adelicBox F`: its measurable space and measure are the Borel structure and Haar measure on $\mathrm{GL}_2(\mathbb{A}_F)$, its central subgroup is all of $\mathbb{A}_F^\times$, and its additive measure is the adelic additive Haar measure conditioned on `adelicBox F`. Let $\xi:\mathbb{A}_F^\times\to\mathbb{C}^\times$ be a homomorphism and $\varphi:\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ continuous and cuspidal automorphic at these pins, that is, $\varphi$ satisfies the predicate `LsXiMemberAt` for the pins' data and $\xi$, and its constant term along $x\mapsto \mathrm{unipotentGL2}(x)$ with respect to the conditioned adelic measure vanishes at every $g$. Let $f$ be a factorizable test function, namely a product of an archimedean factor which is smooth in the matrix entries and compactly supported with a locally constant compactly supported factor at the finite places, and let $B$ lie in the Schwartz–Bruhat space of $\mathbb{A}_F$. Let $\Phi$ satisfy $\Phi(h)=\int_{\mathbb{A}_F} B(x)\,(\varphi * f)(h\,\mathrm{unipotentGL2}(x))\,dx$ for all $h$, where $(\varphi*f)(g)=\int_{\mathrm{GL}_2(\mathbb{A}_F)}\varphi(gy)f(y)\,dy$. Let $\psi$ be an additive character of $\mathbb{A}_F$ that is continuous, nontrivial and trivial on $F$, and let $\chi:\mathbb{A}_F^\times\to\mathbb{C}^\times$ be a continuous homomorphism trivial on principal ideles; let $\nu$ be a Haar measure on $\mathbb{A}_F^\times$ with a Borel structure. Then there are a real $\sigma_1$ and an entire function $Z:\mathbb{C}\to\mathbb{C}$ such that for every $s$ with $\mathrm{Re}\,s>\sigma_1$ the function $a\mapsto W_1(\mathrm{diag}(a,1))\,\chi(a)\,\|a\|^{s-1}$ is $\nu$-integrable and its $\nu$-integral equals $Z(s)$; here $W_1(g)=\int \Phi(\mathrm{unipotentGL2}(x)\,g)\,\psi(-x)\,dx$ against the conditioned adelic measure, and $\|a\|$ is the idele norm given by the distributive Haar character.
--
--   This is the global half of the analytic continuation of the $\mathrm{GL}_2$ zeta integral attached to the first Whittaker coefficient of a smoothed cusp form, as in Jacquet–Langlands' treatment, stated without local representation theory: entirety of $Z$ together with its integral representation in a right half-plane. It feeds the construction of the twisted Euler product, [`AutomorphicForm.exists_differentiable_hasProd_eulerProduct_twist_of_isArithGenuineCuspRealizable`](thm.html#AutomorphicForm.exists_differentiable_hasProd_eulerProduct_twist_of_isArithGenuineCuspRealizable).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_differentiable_forall_integral_zetaIntegrand_whittakerCoefficient_unipotentAverage_eq.lean

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

theorem AutomorphicForm.exists_differentiable_forall_integral_zetaIntegrand_whittakerCoefficient_unipotentAverage_eq
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
    ∃ σ₁ : ℝ, ∃ Z : ℂ → ℂ, Differentiable ℂ Z ∧
      ∀ s : ℂ, σ₁ < s.re →
        Integrable (zetaIntegrand
          (fun g => whittakerCoefficient F
            (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ψ Φ 1 g) χ s) ν ∧
        (∫ a, zetaIntegrand
          (fun g => whittakerCoefficient F
            (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ψ Φ 1 g) χ s a ∂ν) = Z s := by sorry
