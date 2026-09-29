-- Prove2me | Theorems.Thm_AutomorphicForm_exists_norm_rightConv_mul_le_of_lt_localHeight_of_isCuspAutomorphicFnAt_of_coversModCentre
-- name    : AutomorphicForm.exists_norm_rightConv_mul_le_of_lt_localHeight_of_isCuspAutomorphicFnAt_of_coversModCentre
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/9883ace9-34fb-5911-8ffb-1f944c39f7be
-- title:
--   High-height boundedness of a smoothed cuspidal function
-- statement:
--   Let $K$ be a number field, let $c,u,d_1,d_2$ be real numbers with $d_1<d_2$, and let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_K)$. Write $W=\bigcup_{x\in T}\,(\,\cdot\,x)[\,\mathfrak S(c,u,d_1,d_2)\,]$ for the union of the right translates by the elements of $T$ of the centre-cut Siegel set `centreCutSiegelSet K c u d₁ d₂`, the set of $g$ whose finite part lies in `finiteIntegralGL2`, with $c\le \mathrm{localHeight}$ of the $w$-component of the archimedean part of $g$, with $\mathrm{xWindowSq}$ of that component at most $u^2$, and with $\mathrm{archDetNorm}_w(g)\in[d_1,d_2]$, for every infinite place $w$; assume `CoversModCentre K W`, i.e. every $g\in\mathrm{GL}_2(\mathbb{A}_K)$ can be moved into $W$ by left multiplication by a point of $\mathrm{GL}_2(K)$ and right multiplication by a central scalar from $\mathbb{A}_K^\times$. Let $P$ be the production pins of $K$ over $W$ with level subgroups $N\mapsto \mathrm{levelOne}(N)\cap\ker(\mathrm{glArch})$, Hecke generators $v\mapsto \mathrm{heckeGen}(v)$ and additive box `adelicBox K`; its centre is the full group $\mathbb{A}_K^\times$, its measure the adelic Haar measure of $\mathrm{GL}_2$, and its additive measure the adelic Haar measure conditioned on `adelicBox K`. Let $\chi$ be a homomorphism from that centre to $\mathbb{C}^\times$ and let $\varphi:\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ be continuous and satisfy `IsCuspAutomorphicFnAt K P χ φ`, that is, $\varphi$ is automorphic at the pins $P$ with character $\chi$ in the sense of the predicate `IsAutomorphicFnAt`, and cuspidal in the sense of `IsCuspidalFn` for the unipotent subgroup `unipotentGL2` and the conditioned additive measure. Let $f$ be a factorizable test function, i.e. $f(g)=f_\infty(\mathrm{glArch}\,g)\,f_{\mathrm{fin}}(\mathrm{glFin}\,g)$ with $f_\infty$ an archimedean and $f_{\mathrm{fin}}$ a finite test factor. Finally let $c',u',d_1',d_2'$ be real with $c'>0$ and $d_1'>0$, and let $t\in\mathrm{GL}_2(\mathbb{A}_K)$. Then there exist real numbers $C_{\mathrm{cap}}$ and $C$ such that for every $s$ in the centre-cut Siegel set with parameters $c',u',d_1',d_2'$ for which some infinite place $w$ satisfies $C_{\mathrm{cap}}<\mathrm{localHeight}$ of the $w$-component of the archimedean part of $s$, one has $\|(\varphi*f)(st)\|\le C$, where $(\varphi*f)(g)=\int \varphi(gx)f(x)\,dx$ against the adelic Haar measure of $\mathrm{GL}_2$.
--
--   This is the boundedness form of Godement's estimate for a cuspidal function smoothed by a test function: high in a translated Siegel set, where the local height at some infinite place exceeds a cap chosen uniformly, the right convolution $\varphi*f$ stays bounded. It feeds the global bound [`AutomorphicForm.isBoundedOnSiegelWindows_rightConv_of_isCuspAutomorphicFnAt_of_coversModCentre`](thm.html#AutomorphicForm.isBoundedOnSiegelWindows_rightConv_of_isCuspAutomorphicFnAt_of_coversModCentre), where the complementary low-height region is handled by compactness.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_norm_rightConv_mul_le_of_lt_localHeight_of_isCuspAutomorphicFnAt_of_coversModCentre.lean

import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_BoundedGenuineCuspRealization
import Definitions.Def_AutomorphicForm_FactorizableTestFn

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

theorem AutomorphicForm.exists_norm_rightConv_mul_le_of_lt_localHeight_of_isCuspAutomorphicFnAt_of_coversModCentre
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
    (hf : IsFactorizableTestFn K f)
    (c' u' d₁' d₂' : ℝ) (t : AdelicGL2 (𝓞 K) K) (hc' : 0 < c') (hd₁' : 0 < d₁') :
    ∃ Ccap C : ℝ, ∀ s ∈ centreCutSiegelSet K c' u' d₁' d₂',
      (∃ w : InfinitePlace K, Ccap < localHeight (archComponent K w (glArch (𝓞 K) K s))) →
        ‖rightConv K φ f (s * t)‖ ≤ C := by sorry
