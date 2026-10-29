-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_bf_new_bv_hjb_all_positive
-- name    : AvramDividend.Classical.avram_ws01e_bf_new_bv_hjb_all_positive
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T00:41:35.35364+00:00
-- url     : https://prove2.me/theorems/e29bf9ce-48dc-4ef4-86f3-793617335670
-- title:
--   Complete actual bounded-variation HJB at every positive reserve from the original above-barrier inequality
-- statement:
--   For any genuine Standing bounded-variation spectrally negative Levy process with q>0 and canonical scale W, the standard generator-integrability and nonpositive-residual hypothesis strictly above the barrier implies the full nonlocal HJB equality at every positive reserve, including the barrier. The below and above regions are handled by the independently submitted source-faithful BV HJB punctured theorem, and the cap itself by the separately submitted unconditional BV cap generator-harmonicity and smooth-fit theorem. No additional regularity, independence or generator assumption is required at or below the barrier.
-- source:
--   Bounded-variation branch of the original AvramDividend.Classical.vcstar_hjb_all_positive_of_generator (edf09308), with exactly its above-barrier hypothesis and the already permitted case assumption X.BoundedVariation. Composes source-faithful BV offspring 857d1aba and the new actual BV cap HJB child once both remotely Proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bf_new_bv_hjb_except_cstar
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bf_new_bv_cstar_hjb_at_cap
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_bf_new_bv_hjb_all_positive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hbv : X.BoundedVariation)
    (hgen : ∀ y : ℝ, (cstar W).toReal < y →
      X.GeneratorIntegrable (vcstar W) y ∧
        X.generator (vcstar W) y - q * vcstar W y ≤ 0) :
    ∀ y : ℝ, 0 < y →
      X.GeneratorIntegrable (vcstar W) y ∧
        max (X.generator (vcstar W) y - q * vcstar W y)
            (1 - deriv (vcstar W) y) = 0 := by sorry
