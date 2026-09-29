-- Prove2me | Theorems.Thm_AutomorphicForm_exists_analyticOnNhd_eq_sub_mul_peterssonIntegral_of_norm_le_archHeight_pow_centreCutSiegelSet
-- name    : AutomorphicForm.exists_analyticOnNhd_eq_sub_mul_peterssonIntegral_of_norm_le_archHeight_pow_centreCutSiegelSet
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/8eb20a2c-4787-527c-bdad-c873898ed24a
-- title:
--   Holomorphy of the Rankin–Selberg slab integral over a centre-cut Siegel cover
-- statement:
--   Let $F$ be a number field, let $w,a,c,u,d_1,d_2$ be reals with $c>0$, let $\iota$ be a finite index type and $t:\iota\to\mathrm{GL}_2(\mathbb A_F)$, and let $\mathcal F\subseteq\mathrm{GL}_2(\mathbb A_F)$ be measurable and contained in $\bigcup_i\,\mathfrak S\cdot t_i$, where $\mathfrak S=$ `centreCutSiegelSet F c u d₁ d₂` consists of the $g$ whose finite component lies in the level-zero subgroup `finiteIntegralGL2` and whose archimedean component satisfies, at every infinite place $v$, the height floor $c\le\|\det\|/\mathrm{rowNormSq}$, the window bound $\mathrm{xWindowSq}\le u^2$, and the determinant cut $\mathrm{archDetNorm}_v(g)\in[d_1,d_2]$. Let $G:\mathbb C\times\mathrm{GL}_2(\mathbb A_F)\to\mathbb C$ be analytic in $s$ on a neighbourhood of $\{\mathrm{re}\,s>a\}$ for each $g$, jointly continuous on $\{\mathrm{re}\,s>a\}\times\mathrm{GL}_2(\mathbb A_F)$, and of uniform moderate growth: for every compact $C\subseteq\{\mathrm{re}\,s>a\}$ and every $i$ there are $M\in\mathbb R$, $N\in\mathbb N$ with $\|G(s,g t_i)\|\le M(1+H_\infty(g))^N$ for $s\in C$, $g\in\mathfrak S$, where $H_\infty(g)=\prod_v(\|\det\|/\mathrm{rowNormSq})^{v.\mathrm{mult}}$ of the archimedean components. Let $x,y$ be continuous, and assume that for every $i$ and $N$ the function $\|x\|\,\|y\|\,(1+H_\infty(g t_i^{-1}))^N\,\|\det g\|^{-w}$ is integrable on $\mathcal F\cap\mathfrak S t_i$ for the adelic Haar measure `adelicGLHaar` on $\mathrm{GL}_2(\mathbb A_F)$, with $\|\cdot\|$ the idele module `TateGlobal.ideleNorm`. Then two things hold: first, $s\mapsto\int_{\mathcal F}x(g)G(s,g)\overline{y(g)}\|\det g\|^{-w}\,dg$ is analytic on a neighbourhood of $\{\mathrm{re}\,s>a\}$; second, for every $s_0\in\mathbb C$, $\sigma_1\in\mathbb R$ and $E:\mathbb C\times\mathrm{GL}_2(\mathbb A_F)\to\mathbb C$ with $G(s,g)=(s-s_0)E(s,g)$ whenever $\mathrm{re}\,s>\sigma_1$, that integral equals $(s-s_0)$ times `peterssonIntegral F w 𝓕 (x·E s) y`, namely $(s-s_0)\int_{\mathcal F}x(g)E(s,g)\overline{y(g)}\|\det g\|^{-w}\,dg$, for all $s$ with $\mathrm{re}\,s>\sigma_1$ and $\mathrm{re}\,s>a$.
--
--   This is the dominated-holomorphy step for the Rankin–Selberg integral in the adelic $\mathrm{GL}_2$ setting: growth of the kernel $G$ on centre-cut Siegel sets against decay of the pair $x,\bar y$ yields local uniform $L^1$ domination on each piece of a finite cover of $\mathcal F$, hence analyticity in $s$, together with the factorisation of the integral when $G$ vanishes to order one at $s_0$. It is used by the two Rankin–Selberg test-data statements producing an analytic family together with the Euler product of `rsEulerPoly`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_analyticOnNhd_eq_sub_mul_peterssonIntegral_of_norm_le_archHeight_pow_centreCutSiegelSet.lean

import Definitions.Def_AutomorphicForm_PeterssonIntegral
import Definitions.Def_AutomorphicForm_WindowedSiegelSet
import Definitions.Def_AutomorphicForm_CentreCutSiegelSet
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_NumberField_AdelicHaar
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.Analysis.Meromorphic.Order

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel
open AutomorphicForm AutomorphicForm.WindowedSiegel Filter Topology

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem AutomorphicForm.exists_analyticOnNhd_eq_sub_mul_peterssonIntegral_of_norm_le_archHeight_pow_centreCutSiegelSet
    (F : Type) [Field F] [NumberField F]
    (w a c u d₁ d₂ : ℝ) (_hc : 0 < c) (ι : Type) [Fintype ι] (t : ι → AdelicGL2 (𝓞 F) F)
    (𝓕 : Set (AdelicGL2 (𝓞 F) F)) (_h𝓕m : MeasurableSet 𝓕)
    (_h𝓕cov : 𝓕 ⊆ ⋃ i, (· * t i) '' centreCutSiegelSet F c u d₁ d₂)
    (G : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
    (_hGan : ∀ g, AnalyticOnNhd ℂ (fun s => G s g) {s : ℂ | a < s.re})
    (_hGc : ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => G p.1 p.2) ({s : ℂ | a < s.re} ×ˢ Set.univ))
    (_hGbd : ∀ (C : Set ℂ), IsCompact C → C ⊆ {s : ℂ | a < s.re} → ∀ i : ι,
      ∃ (M : ℝ) (N : ℕ), ∀ s ∈ C, ∀ g ∈ centreCutSiegelSet F c u d₁ d₂,
        ‖G s (g * t i)‖ ≤ M * (1 + archHeight F (glArch (𝓞 F) F g)) ^ N)
    (x y : AdelicGL2 (𝓞 F) F → ℂ) (_hxc : Continuous x) (_hyc : Continuous y)
    (_hdecay : ∀ (i : ι) (N : ℕ), IntegrableOn
      (fun g => ‖x g‖ * ‖y g‖ * (1 + archHeight F (glArch (𝓞 F) F (g * (t i)⁻¹))) ^ N *
        NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ (-w))
      (𝓕 ∩ (· * t i) '' centreCutSiegelSet F c u d₁ d₂) (adelicGLHaar (Fin 2) (𝓞 F) F)) :
    AnalyticOnNhd ℂ (fun s : ℂ => ∫ g in 𝓕, x g * G s g * (starRingEnd ℂ) (y g) *
        ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ (-w) : ℝ) : ℂ)
        ∂(adelicGLHaar (Fin 2) (𝓞 F) F)) {s : ℂ | a < s.re} ∧
    ∀ (s₀ : ℂ) (σ₁ : ℝ) (E : ℂ → AdelicGL2 (𝓞 F) F → ℂ),
      (∀ (s : ℂ) (g : AdelicGL2 (𝓞 F) F), σ₁ < s.re → G s g = (s - s₀) * E s g) →
      ∀ s : ℂ, σ₁ < s.re → a < s.re →
        (∫ g in 𝓕, x g * G s g * (starRingEnd ℂ) (y g) *
          ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ (-w) : ℝ) : ℂ)
          ∂(adelicGLHaar (Fin 2) (𝓞 F) F)) =
        (s - s₀) * peterssonIntegral F w 𝓕 (fun g => x g * E s g) y := by sorry
