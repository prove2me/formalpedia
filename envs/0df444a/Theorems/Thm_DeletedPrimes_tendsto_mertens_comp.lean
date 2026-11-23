-- Prove2me | Theorems.Thm_DeletedPrimes_tendsto_mertens_comp
-- name    : DeletedPrimes.tendsto_mertens_comp
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T21:49:29.852213+00:00
-- url     : https://prove2.me/theorems/e709acc5-e785-414e-ab7c-0233633cb24c
-- title:
--   Deleted Primes: tendsto mertens comp
-- statement:
--   The Deleted Primes construction uses the tendsto mertens comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/GoodScales.lean#L133-L141
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/GoodScales.lean#L133-L141

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_GoodScales
set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
open Classical

theorem DeletedPrimes.tendsto_mertens_comp {S : Set ℕ} {α m : ℝ} (hM : MertensLaw S α m) {u : ℝ → ℝ} {c : ℝ}
    (hu : Tendsto u atTop atTop)
    (hlog : Tendsto (fun x => Real.log (u x) / Real.log x) atTop (𝓝 c)) :
    Tendsto (fun x => mertensSum S α (u x) / Real.log x) atTop (𝓝 (m * c)) := by sorry
