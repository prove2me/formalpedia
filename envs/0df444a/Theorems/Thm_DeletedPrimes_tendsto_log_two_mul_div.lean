-- Prove2me | Theorems.Thm_DeletedPrimes_tendsto_log_two_mul_div
-- name    : DeletedPrimes.tendsto_log_two_mul_div
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:56:12.617803+00:00
-- url     : https://prove2.me/theorems/39910abb-4ec1-4a47-bce9-a49922ec6c7b
-- title:
--   Deleted Primes: tendsto log two mul div
-- statement:
--   The Deleted Primes construction uses the tendsto log two mul div property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/GoodScales.lean#L149-L158
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/GoodScales.lean#L149-L158

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_GoodScales
set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
open Classical

theorem DeletedPrimes.tendsto_log_two_mul_div :
    Tendsto (fun x : ℝ => Real.log (2 * x) / Real.log x) atTop (𝓝 1) := by sorry
