-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_original_fourth_deficit_integrable
-- name    : AvramDividend.Classical.avram_p2_original_fourth_deficit_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T00:15:13.162298+00:00
-- url     : https://prove2.me/theorems/b9f699ab-d8bc-4499-9885-5651fe84b776
-- title:
--   Fourth exponential deficit of the original Lévy increment is integrable at every time
-- statement:
--   For the same original spectrally negative Lévy process X and its actual probability measure P, the fourth power (exp(X_t)-1)^4 is integrable at each nonnegative time. Expand the fourth power as a finite signed combination of exp(k X_t) for k=0,1,2,3,4 and apply the genuine original-process Laplace integrability axiom. This permits conversion of the fourth-deficit real expectation into its ENNReal lintegral for the separated-band Markov probability estimate.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_original_fourth_deficit_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℝ≥0) :
    Integrable (fun ω => (Real.exp (X.X t ω) - 1) ^ 4) P := by sorry
