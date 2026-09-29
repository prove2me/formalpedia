-- Prove2me | Theorems.Thm_AvramDividend_BailOut_lemma3_iii_antitone_in_barrier
-- name    : AvramDividend.BailOut.lemma3_iii_antitone_in_barrier
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T18:07:59.551158+00:00
-- url     : https://prove2.me/theorems/da2d3a9b-c461-4558-826a-7875e21b6ba5
-- title:
--   Lemma 3(iii) — $a\mapsto\bar v_a(x)$ is nonincreasing for $a>d^*$
-- statement:
--   Let $X$ be a spectrally negative Lévy process satisfying the standing assumptions, $q>0$, $\varphi>1$, and let $\bar v_a$ and $d^*$ be as in (5.4) and (5.6). Then for every $x>0$, the map
--
--   $$a\longmapsto\bar v_a(x)$$
--
--   is nonincreasing on $(d^*,\infty)$.
--
--   It is used in the proof of Lemma 5 to compare $\bar v_{d^*}$ with the values of higher barriers.
-- source:
--   Avram, Palmowski, Pistorius, On the optimal dividend problem for a spectrally negative Lévy process, arXiv:math/0702893v1, p. 16, Lemma 3(iii)

import Mathlib
import Definitions.Def_AvramDividend_BailOut_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_BailOut_ScaleFunction
import Definitions.Def_AvramDividend_BailOut_BarrierCandidates

open MeasureTheory
open scoped NNReal ENNReal

namespace AvramDividend.BailOut

theorem lemma3_iii_antitone_in_barrier {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} (Lv : SpectrallyNegativeLevy P 𝓕) (hL : Lv.StandingAssumptions)
    {q : ℝ} (hq : 0 < q) {φ : ℝ} (hφ : 1 < φ)
    {W : ℝ → ℝ} (hW : Lv.triplet.IsScaleFunction q W) :
    ∀ x : ℝ, 0 < x →
      AntitoneOn (fun a => vbar Lv q φ W a x) (Set.Ioi (dStar q φ W).toReal) := by sorry

end AvramDividend.BailOut
