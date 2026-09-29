-- Prove2me | Theorems.Thm_AutomorphicForm_exists_norm_rightConv_mul_le_mul_inv_archHeight_pow_of_lt_localHeight_of_isCuspAutomorphicFnAt_of_coversModCentre
-- name    : AutomorphicForm.exists_norm_rightConv_mul_le_mul_inv_archHeight_pow_of_lt_localHeight_of_isCuspAutomorphicFnAt_of_coversModCentre
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/c1af6f9a-76a1-58ec-b0c1-3158d9c2c53e
-- title:
--   Rapid decay of smoothed cusp forms in the cusp
-- statement:
--   Let $K$ be a number field, let $c,u,d_1,d_2$ be reals with $d_1<d_2$, and let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_K)$. Put $W=\bigcup_{x\in T}\{s x : s\in \Sigma\}$, where $\Sigma=$ `centreCutSiegelSet K c u d₁ d₂` consists of those $g$ whose finite part lies in `finiteIntegralGL2`, with $c\le \mathrm{localHeight}$ of the $w$-component of the archimedean part, $\mathrm{xWindowSq}$ of that component at most $u^2$, and $\mathrm{archDetNorm}_w(g)\in[d_1,d_2]$, for every infinite place $w$. Assume `CoversModCentre K W`: every $g\in\mathrm{GL}_2(\mathbb{A}_K)$ admits $\gamma\in\mathrm{GL}_2(K)$ and $z\in\mathbb{A}_K^\times$ with $\mathrm{globalPoints}(\gamma)\,g\,\mathrm{centralScalar}(z)\in W$. Let $\chi$ be a character, valued in $\mathbb{C}^\times$, of the group $Z=\top$ of the pins `productionPinsOf` built from $W$, the levels $N\mapsto$ `levelOne` $\sqcap$ `finiteAdelicGL2Subgroup`, the Hecke generators `heckeGen`, and the box `adelicBox K`. Let $\varphi:\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ be continuous and satisfy `IsCuspAutomorphicFnAt` for these pins and $\chi$, i.e. `IsAutomorphicFnAt` together with the vanishing condition `IsCuspidalFn` along `unipotentGL2` for the measure obtained by conditioning the adelic additive Haar measure on `adelicBox K`. Let $f$ be factorizable, i.e. $f(g)=f_\infty(\mathrm{glArch}\,g)\,f_{\mathrm{fin}}(\mathrm{glFin}\,g)$ with $f_\infty$ an arch test factor and $f_{\mathrm{fin}}$ a finite test factor. Finally let $c',u',d_1',d_2'$ be reals with $c'>0$ and $d_1'>0$, let $t\in\mathrm{GL}_2(\mathbb{A}_K)$ and $k\in\mathbb{N}$. Then there exist reals $C_{\mathrm{cap}}$ and $C$ such that for every $s\in$ `centreCutSiegelSet K c' u' d₁' d₂'` for which some infinite place $w$ has $\mathrm{localHeight}$ of the $w$-component of $\mathrm{glArch}(s)$ exceeding $C_{\mathrm{cap}}$, the right convolution $(\varphi*f)(g)=\int \varphi(gy)f(y)\,dy$ against the adelic $\mathrm{GL}_2$ Haar measure satisfies $\|(\varphi*f)(st)\|\le C\,(\mathrm{archHeight}(\mathrm{glArch}\,s))^{-k}$, where $\mathrm{archHeight}=\prod_w \mathrm{localHeight}^{\,\mathrm{mult}(w)}$ over the infinite places.
--
--   This is the rapid decay of a smoothed cusp form high in the cusp, in the window-$L^2$ adelic setting used here: above a height cap on a centre-cut Siegel set, $\varphi*f$ decays faster than any prescribed power of the archimedean height, uniformly after a fixed right translation by $t$. It feeds the bounds for $\varphi*f$ in terms of the full adelic height, the square-integrability of $\varphi*f$ against powers of the height and the idele norm, and the statement that $\varphi*f$ is rapidly decreasing on Siegel sets.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_norm_rightConv_mul_le_mul_inv_archHeight_pow_of_lt_localHeight_of_isCuspAutomorphicFnAt_of_coversModCentre.lean

import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_BoundedGenuineCuspRealization
import Definitions.Def_AutomorphicForm_FactorizableTestFn

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

theorem AutomorphicForm.exists_norm_rightConv_mul_le_mul_inv_archHeight_pow_of_lt_localHeight_of_isCuspAutomorphicFnAt_of_coversModCentre
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
    (c' u' d₁' d₂' : ℝ) (t : AdelicGL2 (𝓞 K) K) (hc' : 0 < c') (hd₁' : 0 < d₁') (k : ℕ) :
    ∃ Ccap C : ℝ, ∀ s ∈ centreCutSiegelSet K c' u' d₁' d₂',
      (∃ w : InfinitePlace K, Ccap < localHeight (archComponent K w (glArch (𝓞 K) K s))) →
        ‖rightConv K φ f (s * t)‖ ≤ C * (archHeight K (glArch (𝓞 K) K s))⁻¹ ^ k := by sorry
