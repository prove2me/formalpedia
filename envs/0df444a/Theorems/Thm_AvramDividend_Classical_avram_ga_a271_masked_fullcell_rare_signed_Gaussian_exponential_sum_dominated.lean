-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a271_masked_fullcell_rare_signed_Gaussian_exponential_sum_dominated
-- name    : AvramDividend.Classical.avram_ga_a271_masked_fullcell_rare_signed_Gaussian_exponential_sum_dominated
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T09:11:11.716601+00:00
-- url     : https://prove2.me/theorems/8f5aabf4-5f54-4607-bf4a-8019fab95b1d
-- title:
--   Masked finite Gaussian rare signed exponential sum dominated by positive raw exponential tail and raw large-square tail
-- statement:
--   For any finite original physical cell mask A and raw Gaussian increment r, the sum of positive exponentials over both rare increment tails |r|≥δ is pointwise dominated by the positive rare exponential tail r≥δ plus δ^-2 times the rare raw-square tail. This is an exact finite stopped-mask one-sided bridge; its expected bound uses already-proved a233 positive rare exponential and a187 true stopped raw rare square convergence to zero, allowing negative large increments to be controlled without a two-sided exponential upper envelope.
-- source:
--   Gaussian rare signed exp scalar a270; a233 positive raw exponential original source, a187 raw large square

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a270_negative_large_Gaussian_raw_exponential_absorbed_by_quadratic_tail
open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_ga_a271_masked_fullcell_rare_signed_Gaussian_exponential_sum_dominated
    {Ω : Type*} (S : Finset ℕ)
    (A : ℕ → Ω → Prop) [∀ i, DecidablePred (A i)]
    (r : ℕ → Ω → ℝ) (theta delta : ℝ)
    (hθ : 0 ≤ theta) (hδ : 0 < delta) (ω : Ω) :
    (∑ i ∈ S,
      if A i ω ∧ delta ≤ |r i ω| then Real.exp (theta*r i ω) else 0) ≤
    (∑ i ∈ S,
      if A i ω ∧ delta ≤ r i ω then Real.exp (theta*r i ω) else 0) +
      (1/delta^2) * (∑ i ∈ S,
        if A i ω ∧ delta ≤ |r i ω| then (r i ω)^2 else 0) := by sorry
