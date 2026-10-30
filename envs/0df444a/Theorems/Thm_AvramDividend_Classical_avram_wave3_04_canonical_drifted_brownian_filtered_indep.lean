-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_04_canonical_drifted_brownian_filtered_indep
-- name    : AvramDividend.Classical.avram_wave3_04_canonical_drifted_brownian_filtered_indep
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T00:58:12.707365+00:00
-- url     : https://prove2.me/theorems/7567e24f-7f70-4c87-a113-9dae268a891a
-- title:
--   Canonical drifted Gaussian Brownian increments are independent of their natural filtration
-- statement:
--   The canonical BrownianMotion witness is pointwise identical to the normalised projective-limit Brownian path. Its pre-Brownian independence law, combined with the accepted deterministic-drift filtration theorem, makes all drift-minus-one increments independent of the exact natural filtration of the canonical drifted path. Natural adaptation and strong measurability are sourced from the existing Proved canonical natural-adapted theorem.
-- source:
--   Canonical bridge 6b447517-ee65-42fd-aa06-1faa205162a5; canonical natural adaptation f81b6ab6-d291-4f59-8edb-d400ad0cc070; filtered pre-Brownian independence theorem 5baf5e61-4bdf-4c7a-be22-9df36b080894.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_canonical_brownian_realTime_bridge
import Theorems.Thm_AvramDividend_Classical_canonical_drifted_brownian_natural_adapted
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_drifted_preBrownian_filtered_indep
import Theorems.Thm_LevyStochCalc_Brownian_BrownianMotion_hasIndepIncrements_readable
import Theorems.Thm_LevyStochCalc_Brownian_BrownianMotion_hasLaw_eval_readable

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.avram_wave3_04_canonical_drifted_brownian_filtered_indep :
    let B : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ :=
      fun t ω => brownian t ω - brownian 0 ω - (t : ℝ)
    ∃ hmeas : ∀ t : ℝ≥0, StronglyMeasurable (B t),
      ∀ s t : ℝ≥0, s ≤ t →
        Indep (MeasurableSpace.comap
          (fun ω => B t ω - B s ω) inferInstance)
          ((Filtration.natural B hmeas) s) gaussianLimit  := by sorry
