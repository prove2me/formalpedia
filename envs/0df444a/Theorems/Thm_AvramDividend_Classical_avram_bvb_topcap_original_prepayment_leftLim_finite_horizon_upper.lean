-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_topcap_original_prepayment_leftLim_finite_horizon_upper
-- name    : AvramDividend.Classical.avram_bvb_topcap_original_prepayment_leftLim_finite_horizon_upper
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T08:12:26.845941+00:00
-- url     : https://prove2.me/theorems/afadb230-69b3-43d0-b1a2-fae30efd1ebd
-- title:
--   Original bounded-variation prepayment left-limit reserve upper envelope on every finite horizon
-- statement:
--   From original BV path domination by drift and nondecreasing dividends, every positive-time prepayment left limit on (0,T] is a.e. bounded above by x+max(T*drift,0). Includes zero reserve and original stochastic path. Derive from proved postpayment source upper envelope and leftLim order passage.
-- source:
--   Missing upper prepayment envelope for topcap original marked kernel count domination 553da8cc; required to replace finite cap bound.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb_topcap_original_prepayment_leftLim_finite_horizon_upper
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 < T) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      0 < t → (t : ℝ) ≤ T →
      Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t ≤
        x + max (T * X.drift) 0 := by sorry
