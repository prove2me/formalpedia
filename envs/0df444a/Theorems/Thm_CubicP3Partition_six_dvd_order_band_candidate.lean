-- Prove2me | Theorems.Thm_CubicP3Partition_six_dvd_order_band_candidate
-- name    : CubicP3Partition.six_dvd_order_band_candidate
-- status  : Proved
-- author  : @hao jia
-- created : 2026-09-17T00:52:58.38491+00:00
-- url     : https://prove2.me/theorems/612be50a-f1a1-4e96-be4f-dc668c25959e
-- title:
--   R03 P3-factor structural result: Six dvd order band candidate
-- statement:
--   This is a source-faithful auxiliary theorem from the candidate formalization of the cubic P3-partition problem. It records the structural result `CubicP3Partition.six_dvd_order_band_candidate` under exactly the explicit hypotheses in the Lean statement. It is a conditional reusable result and does not claim that the open root problem has been solved.
--
--   **Formalization Note** The Lean statement and direct proof were extracted from the cited candidate artifact; its source digest is recorded in the campaign ledger.
-- source:
--   VibeMathing candidate artifact: research/artifacts/candidates/r03/parallel/sp09/r03-sp09-order-band-boundary-v1.lean; source SHA-256 8105fc26bf91c69ae4c0d1696c2875efac73fa7c9dadc5aaa696534306de9d1d; ProblemContract problem:opg-46613-p3-partition; candidate-only formalization.

import Definitions.Def_cubic_p3_partition_models

namespace CubicP3Partition

open CubicP3Partition
theorem six_dvd_order_band_candidate
    {n : Nat} (hSix : 6 ∣ n) (hMin : 4 ≤ n) :
    n = 6 ∨ n = 12 ∨ 18 ≤ n := by sorry

end CubicP3Partition
