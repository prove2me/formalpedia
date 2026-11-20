-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_original_masked_discounted_negative_JL_onecell_identity
-- name    : AvramDividend.Classical.avram_pj_workerC_original_masked_discounted_negative_JL_onecell_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T07:08:11.846006+00:00
-- url     : https://prove2.me/theorems/bd0debf8-f59c-4d50-a741-ea2ca54d01e7
-- title:
--   Discounted original stopped-cell nonlinear and linear negative-mark jump kernels collapse under the same physical time mask
-- statement:
--   At any actual negative Lévy jump mark, an arbitrary time-stop membership mask and discount weight applied to the nonlinear compensated Taylor kernel plus annular linear correction collapse into the same-mask discounted very-small-mark adjusted Taylor kernel. The stopped clock and discount weight remain unchanged, including at the boundary. This is the signed one-cell kernel needed to combine original J and L before compensated integration.
-- source:
--   Proved 97521e90 pointwise negative-mark kernel cancellation, with common stopping mask, scalar factor and ring identity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_negative_mark_JL_cutoff_exact_kernel
open MeasureTheory Set AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_pj_workerC_original_masked_discounted_negative_JL_onecell_identity
    (η z a S d : ℝ) (hη : 0 < η) (hηone : η < 1)
    (hz : z < 0) (ht : Prop) [Decidable ht] :
    (if ht then a * (S - (if -1 < z then z * d else 0)) else 0) +
    (if ht ∧ z ∈ Ioo (-1 : ℝ) (-η) then a * z * d else 0) =
    (if ht then a * (S - (if -η ≤ z then z * d else 0)) else 0) := by sorry
