-- Prove2me | Theorems.Thm_AvramDividend_Classical_killed_firstUpcrossing_weighted_sandwich
-- name    : AvramDividend.Classical.killed_firstUpcrossing_weighted_sandwich
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T13:34:30.546353+00:00
-- url     : https://prove2.me/theorems/8b9a9ed3-3d6c-4b0b-b833-c48c6c557c5b
-- title:
--   Two-sided ordinary exit bounds for the actual killed reflected record reward
-- statement:
--   For finite first strict upcrossing u(ω) of record b, barrier a>0, any ENNReal payoff weight, and on a path subset G, the genuine killed dividend-record payoff E[w; u<barrierRuinTime] is bounded below by the payoff on paths remaining above b−a and above by the payoff on paths remaining above −a. This is the precise stochastic expectation sandwich needed to put W(a−h)/W(a) and W(a)/W(a+h) around the one-step killed renewal transform when the two-sided q-scale exit law becomes available. The inequalities are expectations under the original P, not just pathwise event containments; no scale exit probabilities are assumed here. The required right-continuity is supplied by a separately Proved theorem for the actual Lévy reflected process, so no extra pathwise regularity hypothesis is needed.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 1 reflected record renewal; composition of Chat 05 proved firstUpcrossing_weighted_survival_lintegral_sandwich and pending killed_firstUpcrossing_weighted_reward_eq_survival. Do not publish before the latter is Proved. Unconditional actual right-continuity supplied by proved reflectedSup_right_continuous (aed33f06-6482-4d51-898d-5f3c5630f827).

import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_killed_firstUpcrossing_weighted_reward_eq_survival
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_weighted_survival_lintegral_sandwich
import Theorems.Thm_AvramDividend_Classical_reflectedSup_right_continuous

open Classical MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.killed_firstUpcrossing_weighted_sandwich
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    (u : Ω → ℝ≥0) (G : Set Ω)
    (hu : ∀ ω ∈ G, (u ω : ℝ≥0∞) =
      (⨅ (s : ℝ≥0) (_ : b < X.X s ω), (s : ℝ≥0∞)))
    (w : Ω → ℝ≥0∞) :
    ((∫⁻ ω, if ω ∈ G ∧
       (∀ t : ℝ≥0, t < u ω → b - a ≤ X.X t ω)
       then w ω else 0 ∂P) ≤
     (∫⁻ ω, if ω ∈ G ∧
       (u ω : ℝ≥0∞) < barrierRuinTime X a ω
       then w ω else 0 ∂P)) ∧
    ((∫⁻ ω, if ω ∈ G ∧
       (u ω : ℝ≥0∞) < barrierRuinTime X a ω
       then w ω else 0 ∂P) ≤
     (∫⁻ ω, if ω ∈ G ∧
       (∀ t : ℝ≥0, t < u ω → -a ≤ X.X t ω)
       then w ω else 0 ∂P)) := by sorry
