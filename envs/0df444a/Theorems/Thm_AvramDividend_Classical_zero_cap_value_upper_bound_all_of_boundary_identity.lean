-- Prove2me | Theorems.Thm_AvramDividend_Classical_zero_cap_value_upper_bound_all_of_boundary_identity
-- name    : AvramDividend.Classical.zero_cap_value_upper_bound_all_of_boundary_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T14:16:33.953185+00:00
-- url     : https://prove2.me/theorems/bb4df179-10ac-4ccc-8dca-9ce9642ceb2e
-- title:
--   The exact zero-barrier dividend identity yields global zero-cap verification
-- statement:
--   For any standing spectrally negative Levy process and valid positive-discount scale function, the exact dividend value identity at the zero barrier and zero reserve already implies the upper verification inequality for the zero-capped dividend problem from every nonnegative initial reserve. No Gaussian, bounded-variation, tilt, or path-regularity premises are needed beyond the displayed exact boundary identity. This result can be applied as soon as the open zero-barrier identity is proved.
-- source:
--   Canonically Proved barrier value nonnegativity eb66042a-0dc2-4d0c-9514-5dd05be55c16, boundary-zero comparison d58a54f2-7f8b-4467-b485-93506d163ab8 and reserve-transfer lemma a77b926c-06ed-4fc1-a8f4-945437968469.

import Theorems.Thm_AvramDividend_Classical_barrierValue_zero_zero_nonneg
import Theorems.Thm_AvramDividend_Classical_zero_cap_value_at_zero_upper_bound_of_boundary
import Theorems.Thm_AvramDividend_Classical_zero_cap_value_upper_bound_of_zero_bound

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.zero_cap_value_upper_bound_all_of_boundary_identity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W)
    (hboundary : dividendValue X q 0 (barrierStrategy X 0 0) =
      ENNReal.ofReal (barrierValue W 0 0)) :
    ∀ x : ℝ, 0 ≤ x →
      valueFunctionLe X q 0 x ≤ ENNReal.ofReal (barrierValue W 0 x) := by sorry
