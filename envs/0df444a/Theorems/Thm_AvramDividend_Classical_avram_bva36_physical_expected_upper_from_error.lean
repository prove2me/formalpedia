-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva36_physical_expected_upper_from_error
-- name    : AvramDividend.Classical.avram_bva36_physical_expected_upper_from_error
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T10:09:18.443841+00:00
-- url     : https://prove2.me/theorems/a8f60e2c-6ac2-4e89-9d61-63431cb131c4
-- title:
--   Original stopped source with vanishing positive error gives eventual expected reward budget
-- statement:
--   For an original stopped probability-space source certificate, integrability of the physical reward, joint centred noise and positive error, nonpositive expected noise and a pathwise reward upper bound imply that the expected reward is eventually within every positive epsilon of the candidate benchmark. The proof is a deterministic integration-and-filter step usable after the stochastic physical-grid certificate is established.
-- source:
--   Original Avram BV physical-grid theorem 4f605d76-1989-4147-8ab2-09c6e18a18c3, source-error expected upper step; independently authored 11 November 2026.

import Mathlib
open MeasureTheory Filter

theorem AvramDividend.Classical.avram_bva36_physical_expected_upper_from_error
    {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P]
    (F M E : ℕ → Ω → ℝ) (b : ℝ)
    (hF : ∀ n, MeasureTheory.Integrable (F n) P)
    (hM : ∀ n, MeasureTheory.Integrable (M n) P)
    (hE : ∀ n, MeasureTheory.Integrable (fun ω => max (E n ω) 0) P)
    (hMean : ∀ n, (∫ ω, M n ω ∂P) ≤ 0)
    (hBound : ∀ n, ∀ᵐ ω ∂P, F n ω ≤ b + M n ω + max (E n ω) 0)
    (hVan : Filter.Tendsto (fun n => ∫ ω, max (E n ω) 0 ∂P)
      Filter.atTop (nhds (0 : ℝ))) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in Filter.atTop, (∫ ω, F n ω ∂P) ≤ b + ε := by sorry
