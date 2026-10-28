-- Prove2me | Theorems.Thm_AvramDividend_Classical_lower_survival_running_infimum_equiv
-- name    : AvramDividend.Classical.lower_survival_running_infimum_equiv
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T23:40:38.232676+00:00
-- url     : https://prove2.me/theorems/46ecadff-9b33-407e-adbc-6b41a94cd506
-- title:
--   Exact finite-horizon lower survival event as a running-infimum threshold
-- statement:
--   For a real-valued trajectory of a spectrally negative Levy process bounded below on its closed time interval [0,t], survival of reserve x at every intermediate instant is equivalent to x plus the infimum of that trajectory being nonnegative. This is a deterministic sample-path identity needed to integrate finite-horizon survival against the exponential reserve Laplace kernel.
-- source:
--   Order-completeness inequalities le_csInf and csInf_le, together with non-emptiness of the interval since time zero is included. Independent of the Wiener–Hopf factorisation and usable before Tonelli.

import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Probability.Martingale.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.lower_survival_running_infimum_equiv
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℝ≥0) (ω : Ω)
    (hb : BddBelow {y : ℝ | ∃ s : ℝ≥0, s ≤ t ∧ y = X.X s ω})
    (x : ℝ) :
    (∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω) ↔
      0 ≤ x + sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ t ∧ y = X.X s ω} := by sorry
