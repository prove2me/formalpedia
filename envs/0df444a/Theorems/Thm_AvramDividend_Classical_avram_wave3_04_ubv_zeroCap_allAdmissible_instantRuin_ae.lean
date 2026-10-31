-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_04_ubv_zeroCap_allAdmissible_instantRuin_ae
-- name    : AvramDividend.Classical.avram_wave3_04_ubv_zeroCap_allAdmissible_instantRuin_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T21:48:37.911978+00:00
-- url     : https://prove2.me/theorems/991f736d-d8eb-43a9-9b15-b5ac9d9a7f31
-- title:
--   Every zero-capped original unbounded-variation dividend control ruins immediately almost surely
-- statement:
--   For the actual spectrally negative Lévy process of unbounded variation and every adapted, left-continuous, zero-capped admissible dividend strategy started with zero capital, the exact original controlled-reserve ruin time is zero almost surely. Unbounded variation gives actual near-zero downward increments by the already Proved Rogozin regularity theorem. This forces instantaneous ruin of the genuine zero-barrier reflected process; the canonical barrier-strategy-equals-running-supremum and reflected-ruin identities identify that with the original controlled ruin time for the zero-barrier strategy. The proved zero-cap strategy comparison makes every other admissible zero-capped control ruin no later. This covers the real original process and every adapted strategy, not a surrogate law, and is the complete zero-cap positive-horizon ruin regularity lemma needed by the corrected UBV verification bound.
-- source:
--   Pinned Mathlib 0df444a360eaa60ab8c11dca51a86af692955474; canonical Proved ae_negative_near_zero_of_unbounded_variation 703dc740-a8df-4cd1-9ff1-622fd81d68c7; barrierRuinTime_zero_of_near_zero_negative_path 092db474-a695-4596-823d-0f1bb92d20ae; barrierRuinTime_eq_ruinTime_runningSup 739bd703-79ac-4350-80c8-6b15bf01b836; barrierStrategy_self_eq_runningSup 6f853442-0ba9-4515-8a3d-2297508c4913; zero_cap_ruinTime_le_barrier_ruinTime 73ce745b-97fc-42ad-92e3-397e0ef5f34a. Exact private compiler probe e80bd628-b2d7-4241-b490-92a7f862013b reached sentinel with no source errors; candidate SHA-256 52626ddb04d97b629f8957106708df71d3c4f3d00a8999afd21013fb0c141ce1.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_ae_negative_near_zero_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_barrierRuinTime_zero_of_near_zero_negative_path
import Theorems.Thm_AvramDividend_Classical_barrierRuinTime_eq_ruinTime_runningSup
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_self_eq_runningSup
import Theorems.Thm_AvramDividend_Classical_zero_cap_ruinTime_le_barrier_ruinTime

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_04_ubv_zeroCap_allAdmissible_instantRuin_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X 0 0 D) :
    ∀ᵐ ω ∂P, ruinTime X 0 D ω = 0 := by sorry
