-- Prove2me | Theorems.Thm_AutomorphicForm_isBoundedOnSiegelWindows_rightConv_of_isCuspAutomorphicFnAt_of_coversModCentre
-- name    : AutomorphicForm.isBoundedOnSiegelWindows_rightConv_of_isCuspAutomorphicFnAt_of_coversModCentre
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/a21297c2-4587-5da1-990d-90ec3e902a96
-- title:
--   Right convolution of a cuspidal function is Siegel-window bounded
-- statement:
--   Let $K$ be a number field, let $c,u,d_1,d_2$ be real numbers with $d_1<d_2$, and let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_K)$. Write $W=\bigcup_{x\in T}\mathfrak{S}\,x$ for the union of the right translates by the elements of $T$ of the centre-cut Siegel set $\mathfrak{S}=$ `centreCutSiegelSet K c u d₁ d₂`, consisting of those $g$ whose finite component lies in `finiteIntegralGL2` and whose archimedean component satisfies, at every infinite place $w$ of $K$, the height floor $c\le$ `localHeight`, the window bound `xWindowSq` $\le u^2$ and `archDetNorm` $w\,g\in[d_1,d_2]$. Assume $W$ covers modulo the centre: every $g\in\mathrm{GL}_2(\mathbb{A}_K)$ admits $\gamma\in\mathrm{GL}_2(K)$ and an idele $z\in\mathbb{A}_K^\times$ with $\gamma g\,z\in W$ (images under `globalPoints` and `centralScalar`). Let $P$ be the production pins over $W$ with level groups $N\mapsto$ `levelOne` $\sqcap$ `finiteAdelicGL2Subgroup`, Hecke generators $v\mapsto$ `heckeGen`, and box `adelicBox K`; thus $P$ carries the Borel structure and Haar measure of $\mathrm{GL}_2(\mathbb{A}_K)$, domain $W$, central subgroup $\top\le\mathbb{A}_K^\times$, and the additive Haar measure of $\mathbb{A}_K$ conditioned on `adelicBox K`. Let $\chi$ be a homomorphism from that central subgroup to $\mathbb{C}^\times$ (no continuity assumed), and let $\varphi:\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ be continuous and cuspidal automorphic at $(P,\chi)$, that is, $\varphi$ satisfies the predicate `LsXiMemberAt` for these data together with `IsCuspidalFn` for the conditioned additive measure and `unipotentGL2`. Let $f$ be a factorizable test function: $f(g)=f_\infty(\mathrm{glArch}\,g)\,f_{\mathrm{fin}}(\mathrm{glFin}\,g)$ with $f_\infty$ an `IsArchTestFactor` and $f_{\mathrm{fin}}$ an `IsFinTestFactor`. Then the right convolution $(\varphi*f)(g)=\int_{\mathrm{GL}_2(\mathbb{A}_K)}\varphi(gx)f(x)\,dx$ is bounded on Siegel windows: for all reals $c',u',d_1',d_2'$ with $c'>0$ and $d_1'>0$ and every finite $T'\subseteq\mathrm{GL}_2(\mathbb{A}_K)$ there is $C$ with $\|(\varphi*f)(g)\|\le C$ for all $g$ in the union of the right translates by $T'$ of `centreCutSiegelSet K c' u' d₁' d₂'`.
--
--   This is the qualitative half of Godement's estimate for smoothed cuspidal functions: convolving a square-integrable cuspidal function against a test function turns an a priori only measurable function into one bounded on every Siegel window, the windows of the conclusion carrying a positive height floor and a positive lower determinant bound which the hypothesis window need not. It is the boundedness input for the construction of bounded genuine cuspidal realizations and for the Whittaker-coefficient estimates built on them.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isBoundedOnSiegelWindows_rightConv_of_isCuspAutomorphicFnAt_of_coversModCentre.lean

import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_BoundedGenuineCuspRealization
import Definitions.Def_AutomorphicForm_FactorizableTestFn

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

theorem AutomorphicForm.isBoundedOnSiegelWindows_rightConv_of_isCuspAutomorphicFnAt_of_coversModCentre
    (K : Type) [Field K] [NumberField K]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (χ : (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)).Z →* ℂˣ)
    (φ : AdelicGL2 (𝓞 K) K → ℂ)
    (hφ : IsCuspAutomorphicFnAt K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) χ φ)
    (hcont : Continuous φ)
    (f : AdelicGL2 (𝓞 K) K → ℂ)
    (hf : IsFactorizableTestFn K f) :
    IsBoundedOnSiegelWindows K (rightConv K φ f) := by sorry
