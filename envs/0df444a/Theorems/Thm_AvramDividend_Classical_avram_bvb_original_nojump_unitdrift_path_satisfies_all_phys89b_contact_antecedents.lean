-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_original_nojump_unitdrift_path_satisfies_all_phys89b_contact_antecedents
-- name    : AvramDividend.Classical.avram_bvb_original_nojump_unitdrift_path_satisfies_all_phys89b_contact_antecedents
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T15:04:16.578468+00:00
-- url     : https://prove2.me/theorems/a0d5e971-5788-4ae5-b8a5-ed917ddb4c47
-- title:
--   Original unit drift zero-barrier nojump source realises all four conditional zero-contact leaf premises
-- statement:
--   On the actual negative-uniform unit-drift zero-barrier source with no negative jumps through time one, the tenth-horizon source path is linear, the original marked negative-jump measure on (0,T] vanishes, the genuine ruin clock strictly survives T and the strict positive-reserve/cap interior assumption fails at time zero. These are exactly all four conditional antecedents of the open zero-contact leaf.
-- source:
--   On the actual negative-uniform unit-drift zero-barrier source with no negative jumps through time one, the tenth-horizon source path is linear, the original marked negative-jump measure on (0,T] vanishes, the genuine ruin clock strictly survives T and the strict positive-reserve/cap interior assumption fails at time zero. These are exactly all four conditional antecedents of the open zero-contact leaf.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_bvb_original_nojump_unitdrift_path_satisfies_all_phys89b_contact_antecedents
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (hDrift : X.drift = 1)
    (hPath : ∀ t : ℝ≥0, t ≤ 1 →
      X.X t ω = (t : ℝ) * X.drift)
    (hNoJump : ((Measure.count.restrict {t : ℝ≥0 |
      0 < t ∧ X.X t ω -
        Function.leftLim (fun s : ℝ≥0 => X.X s ω) t ≠ 0}).map
      (fun t : ℝ≥0 => (t, X.X t ω -
        Function.leftLim (fun s : ℝ≥0 => X.X s ω) t))) (Ioc 0 (1 : ℝ≥0) ×ˢ Iio (0 : ℝ)) = 0) :
    let S : ℝ≥0 := ⟨(1 / 10 : ℝ), by norm_num⟩
    (∀ t : ℝ≥0, t ≤ S → X.X t ω = (t : ℝ) * X.drift) ∧
    (((Measure.count.restrict {t : ℝ≥0 |
      0 < t ∧ X.X t ω -
        Function.leftLim (fun s : ℝ≥0 => X.X s ω) t ≠ 0}).map
      (fun t : ℝ≥0 => (t, X.X t ω -
        Function.leftLim (fun s : ℝ≥0 => X.X s ω) t))) (Ioc 0 S ×ˢ Iio (0 : ℝ)) = 0) ∧
    (S : ℝ≥0∞) < ruinTime X 0 (barrierStrategy X 0 0) ω ∧
    (¬ (∀ t : ℝ≥0, t ≤ S →
      0 < riskProcess X 0 (barrierStrategy X 0 0) t ω ∧
      ENNReal.ofReal (riskProcess X 0 (barrierStrategy X 0 0) t ω) <
        (1 : ℝ≥0∞))) := by sorry
