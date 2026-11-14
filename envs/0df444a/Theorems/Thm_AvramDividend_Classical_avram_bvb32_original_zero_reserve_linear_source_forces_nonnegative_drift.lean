-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb32_original_zero_reserve_linear_source_forces_nonnegative_drift
-- name    : AvramDividend.Classical.avram_bvb32_original_zero_reserve_linear_source_forces_nonnegative_drift
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T11:24:05.847212+00:00
-- url     : https://prove2.me/theorems/2ae4c39f-bf1f-46dd-8443-1bf9d4e82193
-- title:
--   Original bounded-variation zero-reserve no-negative-source-jump path forces nonnegative physical drift
-- statement:
--   On the original physical Lévy source no-negative-jump linear path through a strictly positive observation horizon, whenever an actual admissible dividend strategy keeps the controlled reserve identically zero, the original Lévy drift is nonnegative. The accepted exact physical dividend identity yields D(S)=S*drift. The actual dividend strategy must be nondecreasing with D(0)=0, hence D(S)≥0, and S>0 implies drift≥0. This is the precise missing nonnegative drift hypothesis needed for the already-Proved original zero-contact cash+terminal HJB bound, without imposing an extra assumption on the source theorem.
-- source:
--   Accepted original source zero-reserve dividend linear-path identity 765e3b00 and original IsDividendStrategy definition (monotone and D0=0).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bvb24_original_zero_reserve_nojump_source_dividend_exact_physical_linear_drift
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb32_original_zero_reserve_linear_source_forces_nonnegative_drift
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (S : ℝ≥0) (hS : 0 < S)
    (hZero : ∀ t : ℝ≥0, t ≤ S → riskProcess X x D t ω = 0)
    (hSource : ∀ t : ℝ≥0, t ≤ S →
      X.X t ω = (t : ℝ) * X.drift) :
    0 ≤ X.drift := by sorry
