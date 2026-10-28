-- Prove2me | Theorems.Thm_AvramDividend_Classical_zero_reflectedSupValue_of_unbounded_ae_no_local_monotone
-- name    : AvramDividend.Classical.zero_reflectedSupValue_of_unbounded_ae_no_local_monotone
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T19:58:50.301376+00:00
-- url     : https://prove2.me/theorems/60111b0f-cfb4-47fd-b88e-8090a08199dc
-- title:
--   Unbounded-variation zero reflected identity from almost-sure local non-monotonicity
-- statement:
--   For an unbounded-variation spectrally negative Lévy process, the q-scale function starts at zero. Almost-sure failure of path monotonicity on every initial interval implies instantaneous zero-barrier ruin. The already verified zero-reflected-supremum theorem under instantaneous ruin then proves the exact zero-barrier scale identity. This weakens the path condition in the existing negative-near-zero conditional theorem and isolates the remaining zero-time sample-path regularity obligation.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 1, zero-barrier unbounded-variation discussion after (3.13); https://arxiv.org/pdf/math/0702893

import Theorems.Thm_AvramDividend_Classical_barrierRuinTime_zero_of_no_local_monotone_path
import Theorems.Thm_AvramDividend_Classical_zero_reflectedSupValue_of_unbounded_instant_ruin

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

/-- Local non-monotonicity is sufficient for unbounded zero-barrier closure. -/
theorem zero_reflectedSupValue_of_unbounded_ae_no_local_monotone
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (hNoMono : ∀ᵐ ω ∂P, ∀ ε : ℝ≥0, 0 < ε →
      ¬ MonotoneOn (fun t : ℝ≥0 => X.X t ω) (Icc 0 ε)) :
    barrierSupValue X 0 q = ENNReal.ofReal (barrierValue W 0 0) := by sorry

end AvramDividend.Classical
