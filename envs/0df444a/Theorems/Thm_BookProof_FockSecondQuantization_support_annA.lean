-- Prove2me | Theorems.Thm_BookProof_FockSecondQuantization_support_annA
-- name    : BookProof.FockSecondQuantization.support_annA
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T14:40:30.355967+00:00
-- url     : https://prove2.me/theorems/a07b22fb-a942-47b1-bdfd-f357e253fa16
-- title:
--   (j : ℕ) (u : FockAlg) : (annA j u).support ⊆ u.support.image (dn j)
-- statement:
--   Lean 4 theorem `BookProof.FockSecondQuantization.support_annA` (module `BookProof.FockSecondQuantization`), source chapter `BookProof/ChapterFockSecondQuantization.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterFockSecondQuantization.lean

-- Generated from ChapterFockSecondQuantization.lean — theorem BookProof.FockSecondQuantization.support_annA
import Mathlib
import Definitions.Def_ChapterFockSecondQuantization
open BookProof.FockSecondQuantization







open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension
open BookProof.HashimotoShiftInvert

noncomputable section

theorem BookProof.FockSecondQuantization.support_annA (j : ℕ) (u : FockAlg) : (annA j u).support ⊆ u.support.image (dn j) := by sorry
