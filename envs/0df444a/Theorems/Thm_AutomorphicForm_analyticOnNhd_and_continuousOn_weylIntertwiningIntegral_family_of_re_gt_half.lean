-- Prove2me | Theorems.Thm_AutomorphicForm_analyticOnNhd_and_continuousOn_weylIntertwiningIntegral_family_of_re_gt_half
-- name    : AutomorphicForm.analyticOnNhd_and_continuousOn_weylIntertwiningIntegral_family_of_re_gt_half
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/3fd95ef9-a87f-5947-9da7-56b215aea7bc
-- title:
--   Holomorphy and joint continuity of the intertwining integral for Re s > 1/2
-- statement:
--   Let $F$ be a number field, and let $\alpha$ be the character of the idele units obtained by composing the distributive Haar character of the adele ring $\mathbb{A}_F$ with the inclusion $\mathbb{R}_{\ge 0} \to \mathbb{R}$ and passing to units. Assume $\alpha$ takes everywhere strictly positive values, via a hypothesis $h\alpha$. Let $\mu,\nu$ be homomorphisms $\mathbb{A}_F^\times \to \mathbb{C}^\times$ which are unitary (each value has complex absolute value $1$) and trivial on the image of $F^\times$, i.e. idele class characters. Let $\varphi : \mathbb{C} \times \mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$ be such that for every $s$ the function $\varphi_s$ satisfies the induction rule $\varphi_s(bg) = \chi_1(b_{11})\chi_2(b_{22})\varphi_s(g)$ for all $g$ and all $b$ in the Borel subgroup (lower left entry zero), where $\chi_1 = \mu\cdot\alpha^{s+1/2}$ and $\chi_2 = \nu\cdot\alpha^{-(s+1/2)}$ in the sense of `etaFst` and `etaSnd`; that each $\varphi_s$ is `IsArchKFinite` (at every infinite place $w$, the right translates of $\varphi_s$ by the subgroup of row isometries at $w$ span a finite-dimensional space) and `IsKfSmooth` (a smooth vector for the finite adelic subgroup); that $\varphi$ is continuous in $(s,g)$ jointly; and that $s \mapsto \varphi_s(g)$ is entire for each $g$. Then, with $\mathbb{A}_F$ carrying its Borel $\sigma$-algebra and additive Haar measure, the Weyl intertwining integral $M(s,g) = \int_{\mathbb{A}_F} \varphi_s(w^{-1} n(x) g)\,dx$, with $w$ the adelic Weyl element and $n(x)$ the upper unipotent matrix, is, for each fixed $g$, analytic on a neighbourhood of the half-plane $\{\operatorname{Re} s > 1/2\}$, and is jointly continuous on $\{\operatorname{Re} s > 1/2\} \times \mathrm{GL}_2(\mathbb{A}_F)$.
--
--   This is the standard holomorphy and joint continuity statement for the $\mathrm{GL}_2$ intertwining operator attached to the Borel induction, on the half-plane of absolute convergence; no analytic continuation beyond $\operatorname{Re} s > 1/2$ is asserted. It feeds the Maass–Selberg computations for pseudo-Eisenstein series in truncated slabs.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_analyticOnNhd_and_continuousOn_weylIntertwiningIntegral_family_of_re_gt_half.lean

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_NumberField_AdelicHaar
import Mathlib.MeasureTheory.Measure.Haar.DistribChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory NumberField NumberField.AdelicHaar
open AutomorphicForm
open scoped NNReal

theorem AutomorphicForm.analyticOnNhd_and_continuousOn_weylIntertwiningIntegral_family_of_re_gt_half
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 F) F μ) (_hν : IsUnitaryChar (𝓞 F) F ν)
      (_hμic : IsIdeleClassChar (𝓞 F) F μ) (_hνic : IsIdeleClassChar (𝓞 F) F ν)
      (φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : ∀ s, IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) (φ s))
      (_hφK : ∀ s, IsArchKFinite F (φ s))
      (_hφf : ∀ s, IsKfSmooth F (φ s))
      (_hφjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => φ p.1 p.2))
      (_hφhol : ∀ g, Differentiable ℂ (fun s => φ s g)),
    letI := adeleBorel (𝓞 F) F
    (∀ g : AdelicGL2 (𝓞 F) F, AnalyticOnNhd ℂ
        (fun s => weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ s) g)
        {s : ℂ | 1 / 2 < s.re}) ∧
    ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F =>
        weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ p.1) p.2)
      ({s : ℂ | 1 / 2 < s.re} ×ˢ Set.univ) := by sorry
