-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_gen8_original_postright_reserve_leftLim_closed_cap
-- name    : AvramDividend.Classical.avram_bv_gen8_original_postright_reserve_leftLim_closed_cap
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T08:39:17.65917+00:00
-- url     : https://prove2.me/theorems/a009975c-0dd8-489b-a69d-57e07e82672e
-- title:
--   The original pre-ruin Lévy post-payment reserve has its genuine left-limit in the closed admissible cap
-- statement:
--   At any active original stopping time, including t=0, the genuine strict-left state of x+X_t-D_(t+) is nonnegative and bounded by the original admissible cap. The proof uses actual Lévy left limits, exact original right-dividend left-limit semantics, and closure of the capped interval.
-- source:
--   Source-exact bridge from Proved d88fd858 postpayment cap at active times, Proved f9c3a5c4 right-dividend left limits, Proved d955d184 time-zero leftLim, and intrinsic SpectrallyNegativeLevy.leftLim. The cap is transported along a nontrivial physical strict-left neighbourhood; no global L1 claim.

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_postrightpayment_reserve_closed_cap
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_leftLim_origin_nnreal
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_rightLimit_leftLimit_eq_dividend

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_gen8_original_postright_reserve_leftLim_closed_cap
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (C : ℝ≥0∞) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (t : ℝ≥0)
    (hactive : t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) :
    let Z : ℝ := Function.leftLim
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
    0 ≤ Z ∧ ENNReal.ofReal Z ≤ C := by sorry
