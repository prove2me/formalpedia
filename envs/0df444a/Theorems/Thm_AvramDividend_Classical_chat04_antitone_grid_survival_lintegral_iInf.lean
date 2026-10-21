-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_antitone_grid_survival_lintegral_iInf
-- name    : AvramDividend.Classical.chat04_antitone_grid_survival_lintegral_iInf
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T07:31:31.516461+00:00
-- url     : https://prove2.me/theorems/2d396c19-7370-4faa-9a16-f40ee1cac452
-- title:
--   Continuity from above of expected nonnegative payoffs over decreasing grid-survival events
-- statement:
--   Let A_n be an antitone (decreasing) sequence of measurable events in a general measurable space with measure P. Let g≥0 be any measurable extended nonnegative payoff with finite initial (unrestricted) integral. Prove the expected payoff restricted to the intersection of all A_n equals the infimum of the sequence of restricted expected payoffs. This is the rigorous continuity-from-above step for refining finite-grid survival events to continuous-time survival, once the stochastic path argument identifies the event intersection. The result assumes no martingale or q-scale harmonicity and works for arbitrary measures and possible ENNReal payoff values, subject only to the finite moment of g. Derive from pinned Mathlib lintegral_iInf via the measurable, antitone family of indicator payoffs, with a direct pointwise intersection-indicator equals infimum proof.
-- source:
--   Pinned Mathlib MeasureTheory.lintegral_iInf (Mathlib.MeasureTheory.Integral.Lebesgue.Sub), MeasureTheory.Measurable.indicator, and Set indicator/membership lemmas. Designed for later use with accepted Chat04 Standing-scale fixed-time integrability and Chat03 grid detection of strict passage.

import Mathlib.MeasureTheory.Integral.Lebesgue.Sub

open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.chat04_antitone_grid_survival_lintegral_iInf
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (A : ℕ → Set Ω) (hA : ∀ n, MeasurableSet (A n))
    (hAnti : Antitone A)
    (g : Ω → ℝ≥0∞) (hg : Measurable g)
    (hFin : (∫⁻ ω, g ω ∂P) ≠ ∞) :
    (∫⁻ ω, (⋂ n, A n).indicator g ω ∂P) =
      ⨅ n, ∫⁻ ω, (A n).indicator g ω ∂P := by sorry
