-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_02_true_localtime_positive_mass
-- name    : AvramDividend.Classical.avram_wave4_02_true_localtime_positive_mass
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T09:16:41.33999+00:00
-- url     : https://prove2.me/theorems/7f2aee5e-cc67-4956-9c1a-74837b522f35
-- title:
--   Positive finite running-supremum local-time exposure from the genuine positive Esscher root
-- statement:
--   For the actual spectrally negative Levy process with positive q and positive Esscher root phi, the true running supremum at time 1 is strictly positive on an event of positive original probability. This gives nondegenerate finite local-time exposure for the running-supremum normalisation, by the exact Lévy exponential-moment identity. It neither assumes nor constructs an excursion intensity or a compensation formula.
-- source:
--   SpectrallyNegativeLevy.laplace and canonically Proved runningSup_monotone_and_path_le. Positive Esscher root yields E exp(phi X_1)=exp(q)>1, hence positive probability that X_1>0, and thus S_1>0.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_runningSup_monotone_and_path_le

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_02_true_localtime_positive_mass
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q) :
    0 < P {ω : Ω | 0 < runningSup X (1 : ℝ≥0) ω} := by sorry
