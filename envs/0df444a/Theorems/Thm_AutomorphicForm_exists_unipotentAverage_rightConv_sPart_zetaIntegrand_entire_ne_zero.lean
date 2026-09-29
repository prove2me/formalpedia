-- Prove2me | Theorems.Thm_AutomorphicForm_exists_unipotentAverage_rightConv_sPart_zetaIntegrand_entire_ne_zero
-- name    : AutomorphicForm.exists_unipotentAverage_rightConv_sPart_zetaIntegrand_entire_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/5353169a-64f6-5b73-937b-8fec173b8a84
-- title:
--   An entire, non-vanishing S-part torus zeta integral
-- statement:
--   Let $F$ be a number field and let $c,u,d_1,d_2$ be reals with $d_1<d_2$, let $T$ be a finite set of elements of $\mathrm{GL}_2(\mathbb{A}_F)$, and put $D=\bigcup_{x\in T}(\cdot\,x)$-translates of the centre-cut Siegel set `centreCutSiegelSet F c u d₁ d₂` (those $g$ whose finite part is integral, whose local height at each infinite place is $\ge c$, whose $x$-window square is $\le u^2$, and whose archimedean determinant norms lie in $[d_1,d_2]$); assume $D$ covers $\mathrm{GL}_2(\mathbb{A}_F)$ modulo $\mathrm{GL}_2(F)$ on the left and central ideles on the right. Let the carrier data be `productionPinsOf F D` with the level subgroups $\mathrm{levelOne}(N)\cap\ker(\text{archimedean projection})$, the Hecke generators $\mathrm{heckeGen}(v)$, and the adelic box as conditioning set; its central group is the whole idele group, and $\xi$ is a character of it. Let $\varphi:\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ be continuous and cuspidal automorphic for these data with character $\xi$ (membership in $L(\xi)$ for the adelic $\mathrm{GL}_2$-Haar measure and $D$, together with vanishing of all unipotent constant terms for the conditioned box measure), and let $f$ be a factorizable test function, i.e. $f(g)=f_\infty(g_\infty)f_{\mathrm{fin}}(g_{\mathrm{fin}})$ with $f_\infty$ smooth of compact support in the archimedean matrix entries and $f_{\mathrm{fin}}$ locally constant of compact support. Let $\psi$ be a continuous non-trivial additive character of $\mathbb{A}_F$ trivial on $F$, and $\chi$ a continuous character of $\mathbb{A}_F^\times$ trivial on $F^\times$. Let $S$ be a finite set of finite places such that $\varphi*f=\mathrm{rightConv}\,F\,\varphi\,f$ is invariant under right translation by $\mathrm{GL}_2(\mathcal{O}_v)$ for every $v\notin S$, let $g_0\in\mathrm{GL}_2(\mathbb{A}_F)$ have all finite matrix entries outside $S$ equal to those of $1$, and let $a_0\in\mathbb{A}_F^\times$ have component $1$ at every $v\notin S$, and assume the $\psi$-Whittaker coefficient of $\varphi*f$ at $\alpha=1$ is non-zero at $\mathrm{diag}(a_0,1)g_0$. Then for every $s_1\in\mathbb{C}$ there exist $B:\mathbb{A}_F\to\mathbb{C}$ and $\Phi:\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ such that: $B$ lies in the Schwartz–Bruhat space of $\mathbb{A}_F$; $B$ is standard factorizable outside $S$, that is, there are functions $B_w$ on the completions at the infinite places and $B_v$ for finite $v$ with $B(x)=\mathbf{1}_{\{x\text{ integral outside }S\}}(x)\prod_w B_w(x_w)\prod_{v\in S}B_v(x_v)$; $\Phi(h)=\int_{\mathbb{A}_F}B(x)\,\bigl(\mathrm{rightConv}\,F\,\varphi\,(y\mapsto f(g_0^{-1}y))\bigr)(h\,n(x))\,dx$ for the adelic additive Haar measure, where $n(x)$ is the upper unipotent matrix; for every $s\in\mathbb{C}$ the integrand $a\mapsto W_\Phi(\mathrm{diag}(a,1))\,\chi(a)\,\lVert a\rVert^{s-1}$, with $W_\Phi$ the $\psi$-Whittaker coefficient of $\Phi$ at $\alpha=1$, is integrable against the $S$-part measure $\nu_S$ (the push-forward under the $S$-part map of idelic Haar measure restricted to the ideles that are units outside $S$); the function $s\mapsto\int W_\Phi(\mathrm{diag}(a,1))\chi(a)\lVert a\rVert^{s-1}\,d\nu_S(a)$ is differentiable on all of $\mathbb{C}$; and its value at $s_1$ is non-zero.
--
--   This is a soft substitute, at the places of $S$ and the archimedean places, for the statement that the Kirillov model of a local representation contains the Schwartz functions: instead of local representation theory, a unipotent average against a Schwartz–Bruhat function $B$ that is the indicator of the local integers outside $S$ converts the non-vanishing of one Whittaker value into an $S$-part torus zeta integral that converges for all $s$, is entire, and is non-zero at a prescribed $s_1$. It supplies the test vector used in [`AutomorphicForm.exists_differentiable_hasProd_eulerProduct_twist_of_isArithGenuineCuspRealizable`](thm.html#AutomorphicForm.exists_differentiable_hasProd_eulerProduct_twist_of_isArithGenuineCuspRealizable), where the entire $S$-part factor is matched against the Euler product over the remaining places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_unipotentAverage_rightConv_sPart_zetaIntegrand_entire_ne_zero.lean

import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_BoundedGenuineCuspRealization
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_NumberField_AdelicFourier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar MeasureTheory
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain NumberField.TateGlobal
open UnramifiedWhittaker

theorem AutomorphicForm.exists_unipotentAverage_rightConv_sPart_zetaIntegrand_entire_ne_zero
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
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsGlobalAddChar F ψ)
    (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hχ : IsIdeleClassChar (𝓞 F) F χ) (hχc : Continuous χ)
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hKS : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S →
      ∀ (kv : GL (Fin 2) (v.adicCompletionIntegers F)) (g : AdelicGL2 (𝓞 F) F),
        rightConv F φ f (g * placeEmbed F v
          (Matrix.GeneralLinearGroup.map
            (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)) kv)) = rightConv F φ f g)
    (g₀ : AdelicGL2 (𝓞 F) F)
    (hg₀ : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → ∀ i j : Fin 2,
      ((g₀ : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2 v =
        ((1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2 v)
    (a₀ : (AdeleRing (𝓞 F) F)ˣ)
    (ha₀ : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → ((a₀ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v = 1)
    (hW : whittakerCoefficient F
        (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ψ (rightConv F φ f) 1 (diagOne a₀ * g₀) ≠ 0)
    (s₁ : ℂ) :
    ∃ (B : AdeleRing (𝓞 F) F → ℂ) (Φ : AdelicGL2 (𝓞 F) F → ℂ),
      B ∈ NumberField.AdelicFourier.schwartzBruhat F ∧
      (∃ (Bi : (w : InfinitePlace F) → w.Completion → ℂ) (Bf : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ),
        IsFactorizableStandardOutside B S Bi Bf) ∧
      (∀ h : AdelicGL2 (𝓞 F) F, Φ h = (letI := adeleBorel (𝓞 F) F
        ∫ x, B x * rightConv F φ (fun y => f (g₀⁻¹ * y)) (h * unipotentGL2 x) ∂(adelicAddHaar (𝓞 F) F))) ∧
      (∀ s : ℂ, Integrable (zetaIntegrand
          (fun g => whittakerCoefficient F
              (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ψ Φ 1 g) χ s) (NumberField.Idele.sPartMeasure F S)) ∧
      Differentiable ℂ (fun s : ℂ => ∫ a, zetaIntegrand
          (fun g => whittakerCoefficient F
              (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ψ Φ 1 g) χ s a ∂(NumberField.Idele.sPartMeasure F S)) ∧
      (∫ a, zetaIntegrand
          (fun g => whittakerCoefficient F
              (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ψ Φ 1 g) χ s₁ a ∂(NumberField.Idele.sPartMeasure F S)) ≠ 0 := by sorry
