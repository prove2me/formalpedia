-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_HermiteCanonical_cre_coe
-- name    : BookProof.NavierStokesFlow.HermiteCanonical.cre_coe
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T11:30:58.541389+00:00
-- url     : https://prove2.me/theorems/9b0064a8-be07-4b48-aed2-47a1b9089aa7
-- title:
--   (x : lpFiniteModes ℕ) (n : ℕ) : (((cre x : lpFiniteModes ℕ) : L2I ℕ) : ℕ → ℂ) n = (Real.sqrt n : ℂ) * ((x : L2I ℕ) : ℕ → ℂ) (n - 1)
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.HermiteCanonical.cre_coe` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesHermiteCanonical.lean — theorem BookProof.NavierStokesFlow.HermiteCanonical.cre_coe
import Mathlib
import Definitions.Def_ChapterNavierStokesHermiteCanonical
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.HermiteCanonical







open scoped ENNReal



open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.HermiteFarisLavine

theorem BookProof.NavierStokesFlow.HermiteCanonical.cre_coe (x : lpFiniteModes ℕ) (n : ℕ) :
    (((cre x : lpFiniteModes ℕ) : L2I ℕ) : ℕ → ℂ) n
      = (Real.sqrt n : ℂ) * ((x : L2I ℕ) : ℕ → ℂ) (n - 1) := by sorry
