-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_HermiteCanonical_ann_cre_coe
-- name    : BookProof.NavierStokesFlow.HermiteCanonical.ann_cre_coe
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T13:32:08.05946+00:00
-- url     : https://prove2.me/theorems/50776e9b-7b4a-4e5e-8135-d36f30205b8c
-- title:
--   (x : lpFiniteModes ℕ) (n : ℕ) : (((ann (cre x) : lpFiniteModes ℕ) : L2I ℕ) : ℕ → ℂ) n = ((n : ℂ) + 1) * ((x : L2I ℕ) : ℕ → ℂ) n
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.HermiteCanonical.ann_cre_coe` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesHermiteCanonical.lean — theorem BookProof.NavierStokesFlow.HermiteCanonical.ann_cre_coe
import Mathlib
import Definitions.Def_ChapterNavierStokesHermiteCanonical
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.HermiteCanonical







open scoped ENNReal



open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.HermiteFarisLavine

theorem BookProof.NavierStokesFlow.HermiteCanonical.ann_cre_coe (x : lpFiniteModes ℕ) (n : ℕ) :
    (((ann (cre x) : lpFiniteModes ℕ) : L2I ℕ) : ℕ → ℂ) n
      = ((n : ℂ) + 1) * ((x : L2I ℕ) : ℕ → ℂ) n := by sorry
