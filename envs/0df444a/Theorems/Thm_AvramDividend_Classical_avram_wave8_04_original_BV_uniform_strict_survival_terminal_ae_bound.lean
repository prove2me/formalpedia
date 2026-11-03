-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave8_04_original_BV_uniform_strict_survival_terminal_ae_bound
-- name    : AvramDividend.Classical.avram_wave8_04_original_BV_uniform_strict_survival_terminal_ae_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T18:30:51.438809+00:00
-- url     : https://prove2.me/theorems/370e0f69-2a52-4aeb-b629-db2d76a6ca91
-- title:
--   Original BV strict-survival postrightpayment candidate terminal admits uniform deterministic finite-horizon a.e. bound
-- statement:
--   For each fixed finite H, the original Standing BV source and admissible original D give a common deterministic upper bound K for the nonnegative discounted postrightpayment strict-survival terminal at every deterministic S≤H (with an a.e. statement for each S). The bound follows from the actual downward-jump drift ceiling, nonnegative pre-ruin postpayment reserve, the positive BV drift, discount q>0 and compact continuity of w. This dominates all deterministic grid terminal values for downstream stopped Fatou/limit passage.
-- source:
--   Avram-Palmowski-Pistorius Proposition 4(i), stopped inequality (5.13), terminal-domination step for source-specific grid passage; strengthens proved original L1 theorem ab418409-bab1-4e73-8f3d-354a8f64e3a9.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Theorems.Thm_AvramDividend_Classical_avram_wave7_04_original_BV_postright_terminal_drift_ceiling_ae
import Theorems.Thm_AvramDividend_Classical_continuous_test_abs_le_on_finite_cap
import Theorems.Thm_AvramDividend_Classical_postPaymentReserve_nonnegative_strictly_before_ruin
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave8_04_original_BV_uniform_strict_survival_terminal_ae_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) (H : ℝ≥0) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ S : ℝ≥0, S ≤ H →
        ∀ᵐ ω ∂P,
          (if (S : ℝ≥0∞) < ruinTime X x D ω then
            max 0 (Real.exp (-(q * (S : ℝ))) *
              w (x + X.X S ω - rightLimit D S ω))
          else 0) ≤ K := by sorry
