-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_lsc_original_stopped_upperstrip_occupation_le_full
-- name    : AvramDividend.Classical.avram_lsc_original_stopped_upperstrip_occupation_le_full
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T08:18:08.515806+00:00
-- url     : https://prove2.me/theorems/747af689-2ea8-450d-90d4-dbc9193dffea
-- title:
--   Original stopped physical uppercap occupation is pathwise dominated by full-horizon occupation
-- statement:
--   For the original Lévy dividend reserve and an actual stopping time, the time spent above any upper cap band before stopping is at most the full-horizon occupation of the same original reserve. Assuming only integrability of the full indicator, the stopped integrability is already established by a Proved original-source lemma. This is the precise pathwise domination needed to control the positive-drift strip charge.
-- source:
--   Avram dividend finite-cap Gaussian expected verification. Directly uses Proved original stopped occupation integrability bd25afc9-d9b0-47cc-9b9d-3c48b51af979. Comparison preserves actual riskProcess and original stopped path.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB54cp_true_original_stopped_upperstrip_postpre_occupation_indicator_integrable
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_lsc_original_stopped_upperstrip_occupation_le_full
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x b : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (n : ℕ) (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (ρ ω : WithTop ℝ≥0)))
    (ω : Ω)
    (hFullI : IntegrableOn
      (fun t : ℝ =>
        if b < riskProcess X x D (Real.toNNReal t) ω
        then (1 : ℝ) else 0)
      (Ioo (0 : ℝ) (n : ℝ)) volume) :
    (∫ t in Ioo (0 : ℝ) (n : ℝ),
      if t < (ρ ω : ℝ) ∧
          b < riskProcess X x D (Real.toNNReal t) ω
      then (1 : ℝ) else 0 ∂volume) ≤
    (∫ t in Ioo (0 : ℝ) (n : ℝ),
      if b < riskProcess X x D (Real.toNNReal t) ω
      then (1 : ℝ) else 0 ∂volume) := by sorry
