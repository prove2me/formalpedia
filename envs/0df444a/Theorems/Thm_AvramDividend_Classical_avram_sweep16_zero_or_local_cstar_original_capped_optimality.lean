-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_sweep16_zero_or_local_cstar_original_capped_optimality
-- name    : AvramDividend.Classical.avram_sweep16_zero_or_local_cstar_original_capped_optimality
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T13:53:08.393548+00:00
-- url     : https://prove2.me/theorems/bf4bbebf-18b8-4a29-9f8b-8b3c5ef95b18
-- title:
--   Original capped value equality at finite cstar from zero-barrier or cap-interval upper estimate
-- statement:
--   For the original finite-barrier reserve problem, the zero-barrier branch already has kernel-proved all-reserve equality. In the complementary branch the verified cap-interval upper bound propagates to every reserve by the separately kernel-proved original above-barrier identity and barrier-attainment lower bound. The disjunction is explicit and does not assume local verification without proving it; the theorem uses only public Proved sources and gives the exact full capped value equality used upstream of the canonical global upper parent.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_sweep16_zero_cstar_original_capped_optimality
import Theorems.Thm_AvramDividend_Classical_avram_sweep16_interior_cstar_capped_upper_yields_global_capped_optimality

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_sweep16_zero_or_local_cstar_original_capped_optimality
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤)
    (h_smooth :
      0 < X.σ ∨ X.BoundedVariation ∨ ContDiffOn ℝ 2 (vcstar W) (Ioi 0))
    (hEither :
      cstar W = 0 ∨
        (∀ x : ℝ, 0 ≤ x → x ≤ (cstar W).toReal →
          valueFunctionLe X q (cstar W) x ≤ ENNReal.ofReal (vcstar W x))) :
    ∀ x : ℝ, 0 ≤ x →
      valueFunctionLe X q (cstar W) x = ENNReal.ofReal (vcstar W x) := by sorry
