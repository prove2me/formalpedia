-- Prove2me | Theorems.Thm_AvramDividend_Classical_runningSup_linear_of_linear_capital_prefix
-- name    : AvramDividend.Classical.runningSup_linear_of_linear_capital_prefix
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T11:53:08.367841+00:00
-- url     : https://prove2.me/theorems/f3f64bf6-377c-4d53-9ed3-b45ad8707681
-- title:
--   A nonnegative-drift linear Lévy path prefix has exactly linear running supremum
-- statement:
--   When the Lévy path equals its nonnegative linear drift at every time up to t, its true running supremum at t equals d*t. Use the previously established identity between runningSup and the raw supremum over the compact time interval, bound every sampled path value by d*t, and observe the bound is attained at the terminal time. This supplies the record-process step needed to convert zero-drift-deficit prefixes into the proven Stieltjes drift-prefix integral lemma.
-- source:
--   Avram et al. (2007), §3.3 finite-jump drift prefix; accepted runningSup_eq_rawSup_nonneg theorem.

import Theorems.Thm_AvramDividend_Classical_runningSup_eq_rawSup_nonneg
import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Mathlib.Data.Real.Basic
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.runningSup_linear_of_linear_capital_prefix
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (t : ℝ≥0)
    (hDrift : 0 ≤ X.drift)
    (hLinear : ∀ u : ℝ≥0, u ≤ t →
      X.X u ω = X.drift * (u : ℝ)) :
    runningSup X t ω = X.drift * (t : ℝ) := by sorry
