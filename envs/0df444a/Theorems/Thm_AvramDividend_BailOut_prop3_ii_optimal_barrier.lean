-- Prove2me | Theorems.Thm_AvramDividend_BailOut_prop3_ii_optimal_barrier
-- name    : AvramDividend.BailOut.prop3_ii_optimal_barrier
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T18:07:10.06964+00:00
-- url     : https://prove2.me/theorems/ecda317e-612c-44ac-ad75-b37b0c5a00b1
-- title:
--   Proposition 3(ii) — $d^*<\infty$ and $\bar v_a\le\bar v_{d^*}$ for all barriers $a$
-- statement:
--   Let $X$ be a spectrally negative Lévy process satisfying the standing assumptions, in particular $\psi'(0+)>-\infty$. Let $q>0$ and $\varphi>1$, and let $\bar v_a$ and $d^*$ be the candidate value (5.4) and the barrier level (5.6). Then $d^*<\infty$ and $\bar\pi_{0,d^*}$ is the best double-barrier strategy for every initial capital:
--
--   $$\bar v_a(x)\le\bar v_{d^*}(x)\qquad\text{for all }x\ge0\text{ and all admissible barrier levels }a\ge0 .$$
--
--   The admissible levels are all $a>0$, and $a=0$ when $X$ has bounded variation.
--
--   Optimality among barrier strategies is the first step of the proof of Theorem 3.
--
--   **Formalization Note** The paper prints the hypothesis as $\psi'(0+)<\infty$, which holds for every spectrally negative process. The operative hypothesis is $\psi'(0+)>-\infty$ (standing assumption of p. 4, Section 5.2), which is the integrability of $X_1$ assumed here. The paper's "$x,a\ge0$" includes $a=0$. Formula (5.4) at $a=0$ is defined only for bounded variation, where it is (5.5), so $a=0$ is included exactly in that case.
-- source:
--   Avram, Palmowski, Pistorius, On the optimal dividend problem for a spectrally negative Lévy process, arXiv:math/0702893v1, p. 15, Proposition 3(ii)

import Mathlib
import Definitions.Def_AvramDividend_BailOut_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_BailOut_ScaleFunction
import Definitions.Def_AvramDividend_BailOut_BarrierCandidates

open MeasureTheory
open scoped NNReal ENNReal

namespace AvramDividend.BailOut

theorem prop3_ii_optimal_barrier {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} (Lv : SpectrallyNegativeLevy P 𝓕) (hL : Lv.StandingAssumptions)
    {q : ℝ} (hq : 0 < q) {φ : ℝ} (hφ : 1 < φ)
    {W : ℝ → ℝ} (hW : Lv.triplet.IsScaleFunction q W) :
    dStar q φ W < ⊤ ∧
      ∀ x a : ℝ, 0 ≤ x → (0 < a ∨ (a = 0 ∧ Lv.triplet.BoundedVariation)) →
        vbar Lv q φ W a x ≤ vbar Lv q φ W (dStar q φ W).toReal x := by sorry

end AvramDividend.BailOut
