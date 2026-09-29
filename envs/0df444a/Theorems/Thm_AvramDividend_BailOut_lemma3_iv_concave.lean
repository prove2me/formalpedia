-- Prove2me | Theorems.Thm_AvramDividend_BailOut_lemma3_iv_concave
-- name    : AvramDividend.BailOut.lemma3_iv_concave
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T18:08:25.722755+00:00
-- url     : https://prove2.me/theorems/9911af38-e64f-4c89-bd8b-ef71d0b00f6c
-- title:
--   Lemma 3(iv) — $\bar v_{d^*}$ is concave on $(0,\infty)$
-- statement:
--   Let $X$ be a spectrally negative Lévy process satisfying the standing assumptions, $q>0$, $\varphi>1$, and let $\bar v_{d^*}$ be the candidate value (5.4) at the barrier level $d^*$ of (5.6). Then
--
--   $$\bar v_{d^*}:(0,\infty)\to\mathbb R\ \text{ is concave.}$$
--
--   Concavity of $\bar v_{d^*}$ is the property of the candidate that the proof of Lemma 5 uses to control $\Gamma\bar v_{d^*}-q\bar v_{d^*}$ above $d^*$.
--
--   **Formalization Note** The paper prints (iv) for $\bar v_a$ with arbitrary $a>0$. Its proof (p. 17) treats only $a=d^*$, and Lemma 5 uses only that case. For $a>d^*$ the printed claim fails in general: just below $a$ the second derivative of $\bar v_a$ tends to $-G(a)/W(a)\ge0$, which is positive whenever $G(a)<0$. The statement is therefore made for $a=d^*$.
-- source:
--   Avram, Palmowski, Pistorius, On the optimal dividend problem for a spectrally negative Lévy process, arXiv:math/0702893v1, p. 16, Lemma 3(iv) (proof p. 17, for a = d*)

import Mathlib
import Definitions.Def_AvramDividend_BailOut_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_BailOut_ScaleFunction
import Definitions.Def_AvramDividend_BailOut_BarrierCandidates

open MeasureTheory
open scoped NNReal ENNReal

namespace AvramDividend.BailOut

theorem lemma3_iv_concave {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} (Lv : SpectrallyNegativeLevy P 𝓕) (hL : Lv.StandingAssumptions)
    {q : ℝ} (hq : 0 < q) {φ : ℝ} (hφ : 1 < φ)
    {W : ℝ → ℝ} (hW : Lv.triplet.IsScaleFunction q W) :
    ConcaveOn ℝ (Set.Ioi 0) (vbar Lv q φ W (dStar q φ W).toReal) := by sorry

end AvramDividend.BailOut
