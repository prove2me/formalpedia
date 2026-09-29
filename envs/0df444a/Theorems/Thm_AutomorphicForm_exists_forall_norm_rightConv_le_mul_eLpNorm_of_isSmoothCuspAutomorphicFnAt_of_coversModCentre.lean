-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_norm_rightConv_le_mul_eLpNorm_of_isSmoothCuspAutomorphicFnAt_of_coversModCentre
-- name    : AutomorphicForm.exists_forall_norm_rightConv_le_mul_eLpNorm_of_isSmoothCuspAutomorphicFnAt_of_coversModCentre
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/dadc5d56-bceb-5fb1-9c1c-b0c20d460e50
-- title:
--   Uniform convolution bound for smooth cusp forms on a Siegel window
-- statement:
--   Let $F$ be a number field, let $c,u,d_1,d_2$ be real numbers with $0<c$, $0<d_1$ and $d_1<d_2$, and let $T$ be a finite set of points of $\mathrm{GL}_2(\mathbb{A}_F)$. Write $D=\bigcup_{x\in T}\{g x : g\in \Sigma\}$, where $\Sigma=$ `centreCutSiegelSet F c u d₁ d₂` is the set of $g$ whose finite component lies in `finiteIntegralGL2` and whose archimedean components satisfy, at every infinite place $w$ of $F$, $c\le$ `localHeight` of the $w$-component, `xWindowSq` of that component $\le u^2$, and `archDetNorm` $w\,g\in[d_1,d_2]$; it is assumed that $D$ satisfies `CoversModCentre`, i.e. every $g\in\mathrm{GL}_2(\mathbb{A}_F)$ can be written with $\gamma g z\in D$ for some $\gamma\in\mathrm{GL}_2(F)$ (acting through `globalPoints`) and some central scalar $z$ from $\mathbb{A}_F^\times$. Let `pins` be `productionPinsOf` applied to $D$, to the levels $N\mapsto$ `levelOne` $\sqcap$ `finiteAdelicGL2Subgroup`, to the Hecke elements $v\mapsto$ `heckeGen`, and to the box `adelicBox F`; its measure on $\mathrm{GL}_2(\mathbb{A}_F)$ is the Haar measure `adelicGLHaar`, its central subgroup is all of $\mathbb{A}_F^\times$, and its adelic measure is the additive adelic Haar measure conditioned on `adelicBox F`. Let $\xi$ be a homomorphism from that central subgroup to $\mathbb{C}^\times$ (no continuity or unitarity assumed), and let $f:\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ be factorizable, i.e. $f(g)=f_\infty(\text{arch part of }g)\,f_{\mathrm f}(\text{finite part of }g)$ with $f_\infty$ an archimedean and $f_{\mathrm f}$ a finite test factor. Then there is a real number $C$ such that for every $\varphi:\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ which is continuous and satisfies `IsSmoothCuspAutomorphicFnAt F pins ξ` — that is, $\varphi$ satisfies the predicate `IsAutomorphicFnAt` for these pins and $\xi$, is cuspidal along `unipotentGL2` for the conditioned adelic measure, and satisfies `IsKfSmooth` — one has, for every $g\in D$, $\|\int \varphi(gx) f(x)\,dx\|\le C\cdot\|\varphi\|_{L^2(D)}$, the integral being against `adelicGLHaar` and the $L^2$-norm being `eLpNorm` for exponent $2$ with respect to `adelicGLHaar` restricted to $D$, converted to a real number.
--
--   This is the uniform form of Godement's estimate for smoothed cuspidal functions: the convolution $\varphi * f$ is bounded on the covering window $D$ by a multiple of the $L^2(D)$-seminorm of $\varphi$, with the constant depending only on $F$, the window parameters, $T$, $\xi$ and $f$, and chosen before $\varphi$. It feeds the class-sum growth estimates and the construction of nonzero right convolutions inside isotypic cuspidal submodules.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_norm_rightConv_le_mul_eLpNorm_of_isSmoothCuspAutomorphicFnAt_of_coversModCentre.lean

import Definitions.Def_AutomorphicForm_SiegelCovering
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_NumberField_AdelicBox

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar MeasureTheory
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

theorem AutomorphicForm.exists_forall_norm_rightConv_le_mul_eLpNorm_of_isSmoothCuspAutomorphicFnAt_of_coversModCentre
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : 0 < c) (hd₁ : 0 < d₁)
    (hd : d₁ < d₂) (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (ξ : (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).Z →* ℂˣ)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f) :
    ∃ C : ℝ, ∀ φ : AdelicGL2 (𝓞 F) F → ℂ,
      IsSmoothCuspAutomorphicFnAt F
          (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
            (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
            (adelicBox F)) ξ φ →
        Continuous φ →
          ∀ g ∈ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂),
            ‖rightConv F φ f g‖ ≤
              C * (eLpNorm φ 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict
                (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))).toReal := by sorry
