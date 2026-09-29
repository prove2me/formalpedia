-- Prove2me | Theorems.Thm_BookProof_FockSecondQuantization_dn_up
-- name    : BookProof.FockSecondQuantization.dn_up
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T13:00:41.723387+00:00
-- url     : https://prove2.me/theorems/51ca56c5-5376-448d-8309-6107ccbc9bd8
-- title:
--   (j : ℕ) (α : Conf) : dn j (up j α) = α
-- statement:
--   Lean 4 theorem `BookProof.FockSecondQuantization.dn_up` (module `BookProof.FockSecondQuantization`), source chapter `BookProof/ChapterFockSecondQuantization.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterFockSecondQuantization.lean

-- Generated from ChapterFockSecondQuantization.lean — theorem BookProof.FockSecondQuantization.dn_up
import Mathlib
import Definitions.Def_ChapterFockSecondQuantization
open BookProof.FockSecondQuantization







open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension
open BookProof.HashimotoShiftInvert

noncomputable section

theorem BookProof.FockSecondQuantization.dn_up (j : ℕ) (α : Conf) : dn j (up j α) = α := by sorry
