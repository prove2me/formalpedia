-- Prove2me | Theorems.Thm_BookProof_FockSecondQuantization_up_dn
-- name    : BookProof.FockSecondQuantization.up_dn
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T13:01:25.378088+00:00
-- url     : https://prove2.me/theorems/face5d09-4ae5-40dc-84cb-ee849336fd79
-- title:
--   (j : ℕ) {α : Conf} (h : 1 ≤ α j) : up j (dn j α) = α
-- statement:
--   Lean 4 theorem `BookProof.FockSecondQuantization.up_dn` (module `BookProof.FockSecondQuantization`), source chapter `BookProof/ChapterFockSecondQuantization.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterFockSecondQuantization.lean

-- Generated from ChapterFockSecondQuantization.lean — theorem BookProof.FockSecondQuantization.up_dn
import Mathlib
import Definitions.Def_ChapterFockSecondQuantization
open BookProof.FockSecondQuantization







open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension
open BookProof.HashimotoShiftInvert

noncomputable section

theorem BookProof.FockSecondQuantization.up_dn (j : ℕ) {α : Conf} (h : 1 ≤ α j) : up j (dn j α) = α := by sorry
