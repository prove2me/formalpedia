-- Prove2me | Theorems.Thm_AutomorphicForm_memLp_two_rightConv_restrict_of_isCuspAutomorphicFnAt_of_coversModCentre_of_pos
-- name    : AutomorphicForm.memLp_two_rightConv_restrict_of_isCuspAutomorphicFnAt_of_coversModCentre_of_pos
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/3f87e786-7eb4-59aa-abd9-f67443466d15
-- title:
--   Square-integrability of φ * f on a centre-cut Siegel window
-- statement:
--   Let $F$ be a number field, let $c,u,d_1,d_2$ be reals with $0<c$ and $d_1<d_2$, and let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_F)$. Write $D=\bigcup_{x\in T}\{g x : g\in \mathfrak{S}\}$, where $\mathfrak{S}=$ `centreCutSiegelSet F c u d₁ d₂` consists of those $g$ whose finite component lies in `finiteIntegralGL2`, whose archimedean component at every infinite place $w$ has local height at least $c$ and $x$-window square at most $u^2$, and with $\mathrm{archDetNorm}_w(g)\in[d_1,d_2]$ for all $w$. Assume $D$ covers modulo the centre: for every $g$ there are $\gamma\in\mathrm{GL}_2(F)$ and an idele unit $z$ with $\gamma g\,z\in D$ (images under `globalPoints` and `centralScalar`). Let the carrier pins be `productionPinsOf` for $D$, the levels $N\mapsto$ `levelOne`$\,\sqcap\,$`finiteAdelicGL2Subgroup`, the Hecke generators `heckeGen`, and the box `adelicBox`; thus the measurable structure is `glBorel`, the measure is `adelicGLHaar`, the central subgroup is all of $\mathbb{A}_F^\times$, and the adelic measure is the Haar measure conditioned on `adelicBox`. Let $\xi$ be a character of that central subgroup into $\mathbb{C}^\times$, and let $\varphi:\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ be continuous and satisfy `IsCuspAutomorphicFnAt` for these pins and $\xi$ (membership in $L(\xi)$ at the pins together with cuspidality along `unipotentGL2`). Let $f$ be a factorizable test function, i.e. $f(g)=f_\infty(g_\infty)f_{\mathrm{fin}}(g_{\mathrm{fin}})$ with an archimedean and a finite test factor. Then the right convolution $g\mapsto\int \varphi(gx)f(x)\,dx$ against adelic Haar measure lies in $L^2$ of the Haar measure restricted to $D$.
--
--   This records that smoothing a continuous cusp form by a factorizable test function preserves square-integrability on a finite union of right translates of a centre-cut Siegel window, the growth statement needed to place $\varphi*f$ in the cuspidal $L^2$ space. It is used in the construction of cuspidal constituents inside isotypic cusp submodules with an archimedean cut-off, and in the production of test data for Rankin–Selberg integrals.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_memLp_two_rightConv_restrict_of_isCuspAutomorphicFnAt_of_coversModCentre_of_pos.lean

import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar MeasureTheory
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain

theorem AutomorphicForm.memLp_two_rightConv_restrict_of_isCuspAutomorphicFnAt_of_coversModCentre_of_pos
    (F : Type) [Field F] [NumberField F]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : 0 < c) (hd : d₁ < d₂)
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
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f) :
    MemLp (rightConv F φ f) 2
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)) := by sorry
