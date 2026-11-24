-- Prove2me | Theorems.Thm_DeletedPrimes_tendsto_kappaK
-- name    : DeletedPrimes.tendsto_kappaK
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:54:16.727892+00:00
-- url     : https://prove2.me/theorems/d9dc4fbe-5289-40a6-8fa3-ce367c00e280
-- title:
--   Deleted Primes: tendsto kappa K
-- statement:
--   The Deleted Primes construction uses the tendsto kappa K property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Exponents.lean#L388-L405
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Exponents.lean#L388-L405

import Mathlib
import Definitions.Def_DeletedPrimes_Exponents
set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section

theorem DeletedPrimes.tendsto_kappaK {α : ℝ} (h1 : α < 1) :
    Tendsto (fun k : ℕ => kappaK k α) atTop (𝓝 (min (1 / 2) (1 - α))) := by sorry
