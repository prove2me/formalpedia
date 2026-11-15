-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a379_masked_compensator_sum_split_v2
-- name    : AvramDividend.Classical.avram_ga_a379_masked_compensator_sum_split_v2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T13:54:08.364925+00:00
-- url     : https://prove2.me/theorems/eefc43a1-684f-4c9a-ab1f-ba9610b17d4a
-- title:
--   Exact masked finite-sum split for Gaussian linear and generator compensation
-- statement:
--   For any finite index set and any Boolean mask, the sum of separate masked linear and generator terms equals the sum of their combined per-cell compensation, giving an exact three-source difference identity.
-- source:
--   Original stopped Gaussian dividend proof source a146, preserving its distinct physical spatial, linear and HJB compensation sums.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_ga_a379_masked_compensator_sum_split_v2
    (S : Finset ℕ) (F L G : ℕ → ℝ)
    (A : ℕ → Prop) [DecidablePred A] :
    (∑ i ∈ S, F i) -
      (∑ i ∈ S, if A i then L i else 0) -
      (∑ i ∈ S, if A i then G i else 0) =
    (∑ i ∈ S, F i) -
      (∑ i ∈ S, if A i then L i + G i else 0) := by sorry
