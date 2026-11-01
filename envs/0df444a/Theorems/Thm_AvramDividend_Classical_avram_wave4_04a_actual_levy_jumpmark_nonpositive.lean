-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_levy_jumpmark_nonpositive
-- name    : AvramDividend.Classical.avram_wave4_04a_actual_levy_jumpmark_nonpositive
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T09:41:07.63301+00:00
-- url     : https://prove2.me/theorems/e95fe5bc-c756-43ca-82d7-acab7078e2eb
-- title:
--   Every genuine positive-time source Lévy jump mark is nonpositive in the actual path
-- statement:
--   For every sample ω and every positive time t, the actual original spectrally negative Lévy path jump ΔX(t,ω)=X_t(ω)−X_{t−}(ω), where X_{t−} is Mathlib's Function.leftLim, is nonpositive. Uses the exact source left-limit and no-positive-jumps fields; strengthens the existing spectral support fact for ν into an exact sample-path mark support fact needed for N_X, without a replacement process.
-- source:
--   Avram–Palmowski–Pistorius (2007), spectral negativity and original jump measure. Source SpectrallyNegativeLevy.leftLim and .noPosJumps, pinned Mathlib leftLim_eq_of_tendsto.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_04a_actual_levy_jumpmark_nonpositive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    ∀ (ω : Ω) (t : ℝ≥0), 0 < t →
      X.X t ω - Function.leftLim (fun s : ℝ≥0 => X.X s ω) t ≤ 0 := by sorry
