-- Prove2me | Theorems.Thm_AutomorphicForm_tendsto_sub_one_half_mul_weylIntertwiningIntegral_sub_nhds_zero_of_flat_family_of_mem_maximalCompactAt_empty
-- name    : AutomorphicForm.tendsto_sub_one_half_mul_weylIntertwiningIntegral_sub_nhds_zero_of_flat_family_of_mem_maximalCompactAt_empty
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/da5b4dd9-b978-54ed-a108-4457fb1a41c9
-- title:
--   Flat families: intertwining integral residue at 1/2 is K_∞-invariant
-- statement:
--   Let $F$ be a number field and let $\alpha \colon (\mathbb{A}_F)^\times \to \mathbb{R}^\times$ be the character obtained from the distributive Haar character of the adele ring $\mathbb{A}_F$ (valued in $\mathbb{R}_{\ge 0}$, pushed into $\mathbb{R}$ and restricted to units), assumed by `hα` to take strictly positive values. Let $\varphi \colon \mathbb{C} \to \mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$ be a family of functions such that: for each $s$, $\varphi_s$ is an induced section for the pair of characters $\alpha^{\,s+1/2}$ and $\alpha^{-(s+1/2)}$ (built by `etaFst`/`etaSnd` from the trivial character and the complex power `cpowChar` of $\alpha$), i.e. $\varphi_s(bg) = \chi_1(\mathrm{diag}_1 b)\,\chi_2(\mathrm{diag}_2 b)\,\varphi_s(g)$ for all $b$ in the adelic Borel subgroup and all $g$; each $\varphi_s$ is archimedean $K$-finite place by place (`IsArchKFinite`) and a smooth vector for the right translation action of the finite adelic $\mathrm{GL}_2$ subgroup (`IsKfSmooth`); $(s,g) \mapsto \varphi_s(g)$ is jointly continuous; $s \mapsto \varphi_s(g)$ is complex differentiable for every $g$; and the family is flat, in the sense that $\varphi_s(k) = \varphi_{s'}(k)$ for all $s,s'$ whenever the finite component of $k$ lies in $\mathrm{GL}_2(\widehat{\mathcal{O}}_F)$ (`finiteIntegralGL2`) and, at every infinite place $w$, the component of $k$ is a row isometry (determinant of norm $1$ and the two columns acting isometrically on the quadratic form $\|x\|^2+\|y\|^2$). Let $k_\infty \in \mathrm{GL}_2(\mathbb{A}_F)$ lie in `maximalCompactAt F ∅`, that is: $k_\infty$ belongs to the adelic maximal compact subgroup (integral finite part, row-isometric archimedean components) and in addition its finite component is trivial at every finite place. Then, with the Borel measurable structure on $\mathbb{A}_F$ and the additive Haar measure `adelicAddHaar`, writing $M(s)\varphi_s(g) = \int_{\mathbb{A}_F} \varphi_s(w^{-1} n(x) g)\,dx$ for the Weyl intertwining integral, the function $s \mapsto (s - 1/2)\bigl(M(s)\varphi_s(k_\infty) - M(s)\varphi_s(1)\bigr)$ tends to $0$ as $s \to 1/2$ within the half-plane $\{\operatorname{Re} s > 1/2\}$.
--
--   This is the archimedean invariance step for the intertwining operator attached to a flat family of degenerate principal series sections: to leading order at $s = 1/2$ the intertwining integral does not see translation by an element of the archimedean maximal compact subgroup with trivial finite part. It feeds the statement comparing $M(s)\varphi_s(g)$ with its value at the identity, on the way to identifying the residual behaviour of the intertwining operator as a constant.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_tendsto_sub_one_half_mul_weylIntertwiningIntegral_sub_nhds_zero_of_flat_family_of_mem_maximalCompactAt_empty.lean

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_NumberField_AdelicHaar
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Mathlib.Analysis.Meromorphic.Order

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel IsDedekindDomain
open AutomorphicForm.WindowedSiegel Filter Topology
open AutomorphicForm
open scoped NNReal

theorem AutomorphicForm.tendsto_sub_one_half_mul_weylIntertwiningIntegral_sub_nhds_zero_of_flat_family_of_mem_maximalCompactAt_empty
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ))
      (φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : ∀ s, IsInducedSection (𝓞 F) F (etaFst 1 α hα s) (etaSnd 1 α hα s) (φ s))
      (_hφK : ∀ s, IsArchKFinite F (φ s))
      (_hφf : ∀ s, IsKfSmooth F (φ s))
      (_hφjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => φ p.1 p.2))
      (_hφhol : ∀ g, Differentiable ℂ (fun s => φ s g))
      (_hφflat : ∀ (s s' : ℂ) (k : AdelicGL2 (𝓞 F) F),
          glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F →
          (∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))) →
          φ s k = φ s' k)
      (kinf : AdelicGL2 (𝓞 F) F) (_hkinf : kinf ∈ maximalCompactAt F ∅),
    letI := NumberField.AdelicHaar.adeleBorel (𝓞 F) F
    Tendsto (fun s : ℂ => (s - 1 / 2) *
        (weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ s) kinf
          - weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ s) 1))
      (𝓝[{s : ℂ | 1 / 2 < s.re}] (1 / 2 : ℂ)) (𝓝 0) := by sorry
