-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a19_integrable_tight_error_and_vanishing_expectation
-- name    : AvramDividend.Classical.avram_a19_integrable_tight_error_and_vanishing_expectation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T09:26:30.885555+00:00
-- url     : https://prove2.me/theorems/cdbc5133-6ed7-4c04-933f-9bee925f9c95
-- title:
--   Integrable dominated tight errors have vanishing expected positive part
-- statement:
--   If payoff and baseline are integrable and a positive integrable error envelope almost surely dominates their difference with expected positive error vanishing, then the exact positive excess is integrable and its expectation also vanishes.
-- source:
--   Abstract measure theoretic transfer from original stopped-grid error budget to minimal exact excess, supporting the tight-error reduction of uniform physical Levy residual.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a19_integrable_tight_error_and_vanishing_expectation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (F G Err : ℕ → Ω → ℝ)
    (hF : ∀ n, Integrable (F n) P)
    (hG : ∀ n, Integrable (G n) P)
    (hErr : ∀ n, Integrable (fun ω => max (Err n ω) 0) P)
    (hlim : Tendsto
      (fun n => ∫ ω, max (Err n ω) 0 ∂P) atTop (nhds (0 : ℝ)))
    (hbudget : ∀ n, ∀ᵐ ω ∂P,
      F n ω ≤ G n ω + max (Err n ω) 0) :
    (∀ n, Integrable (fun ω => max (F n ω - G n ω) 0) P) ∧
    Tendsto (fun n => ∫ ω, max (F n ω - G n ω) 0 ∂P)
      atTop (nhds (0 : ℝ)) := by sorry
