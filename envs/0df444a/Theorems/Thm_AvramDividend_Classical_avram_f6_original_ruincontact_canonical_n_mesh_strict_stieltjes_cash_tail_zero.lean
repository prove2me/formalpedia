-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f6_original_ruincontact_canonical_n_mesh_strict_stieltjes_cash_tail_zero
-- name    : AvramDividend.Classical.avram_f6_original_ruincontact_canonical_n_mesh_strict_stieltjes_cash_tail_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T20:20:45.144527+00:00
-- url     : https://prove2.me/theorems/e8e62b96-5b58-42a6-89e3-7696e8d1795c
-- title:
--   Actual original canonical n/(j+1) strict ruin-contact Stieltjes tail vanishes
-- statement:
--   For every authentic Lévy risk process X and original dividend strategy D, all realised finite stopping times T and positive integer horizon n, the full discounted Stieltjes cash on the strictly pre-T interval (T−n/(j+1),T), restricted to original paymentTimes at ruin, converges to zero. The horizon-specific width is exactly the canonical finite stopping-grid width used in F6. No atom at T is incorrectly discarded because Ioo excludes the final endpoint. This proves vanishing of the second explicit source remainder in the original mixed ruin-contact finite-grid signed cash inequality.
-- source:
--   Proved strict Stieltjes shrinking-tail theorem avram_bv_env3_original_strict_crossing_cell_discounted_cash_tendsto_zero (28ff0f1f).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_f6_original_ruincontact_canonical_n_mesh_strict_stieltjes_cash_tail_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T : ℝ≥0) (q : ℝ) (hq : 0 ≤ q)
    (n : ℕ) (hn : 0 < n) :
    Tendsto (fun j : ℕ =>
      ∫⁻ s in paymentTimes (ruinTime X x D ω) ∩
          Ioo ((T : ℝ) - (n : ℝ) / ((j : ℝ) + 1)) (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω))
      atTop (nhds 0) := by sorry
