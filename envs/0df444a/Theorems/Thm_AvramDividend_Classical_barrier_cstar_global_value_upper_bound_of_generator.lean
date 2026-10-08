-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrier_cstar_global_value_upper_bound_of_generator
-- name    : AvramDividend.Classical.barrier_cstar_global_value_upper_bound_of_generator
-- status  : Open
-- author  : @WillR
-- created : 2026-10-07T10:11:46.315997+00:00
-- url     : https://prove2.me/theorems/ba2b3f45-a65f-4160-9d9b-ee887c67ade9
-- title:
--   Global verification upper bound at c* under the generator inequality above the barrier
-- statement:
--   Assume the hypotheses of Theorem 2 and, in addition, that above the finite optimal barrier c* the generator of vc* is integrable and satisfies Gamma vc* - q vc* <= 0. Then for every x>=0 the unrestricted classical dividend value function is bounded above by vc*(x). This is the verification/supermartingale half of Theorem 2(ii); attainment by the barrier policy is a separate obligation.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 4(i), Lemma 4, and Theorem 2(ii), pp. 16-21.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem barrier_cstar_global_value_upper_bound_of_generator {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨ ContDiffOn ℝ 2 (vcstar W) (Ioi 0))
    (hgen : ∀ y : ℝ, (cstar W).toReal < y →
      X.GeneratorIntegrable (vcstar W) y ∧
        X.generator (vcstar W) y - q * vcstar W y ≤ 0) :
    ∀ x : ℝ, 0 ≤ x →
      valueFunction X q x ≤ ENNReal.ofReal (vcstar W x) := by sorry

end AvramDividend.Classical
