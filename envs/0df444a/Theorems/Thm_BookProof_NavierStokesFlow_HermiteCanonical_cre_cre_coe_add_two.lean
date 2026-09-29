-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_HermiteCanonical_cre_cre_coe_add_two
-- name    : BookProof.NavierStokesFlow.HermiteCanonical.cre_cre_coe_add_two
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T13:27:35.502678+00:00
-- url     : https://prove2.me/theorems/c105980c-f127-4bd1-830e-42350ff3f8a0
-- title:
--   (x : lpFiniteModes ℕ) (k : ℕ) : (((cre (cre x) : lpFiniteModes ℕ) : L2I ℕ) : ℕ → ℂ) (k + 2) = (Real.sqrt ((k : ℝ) + 2) : ℂ) * (Real.sqrt ((k : ℝ) + 1) : ℂ) * ((x : L2I ℕ) : ℕ → ℂ) k
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.HermiteCanonical.cre_cre_coe_add_two` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesHermiteCanonical.lean — theorem BookProof.NavierStokesFlow.HermiteCanonical.cre_cre_coe_add_two
import Mathlib
import Definitions.Def_ChapterNavierStokesHermiteCanonical
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.HermiteCanonical







open scoped ENNReal



open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.HermiteFarisLavine

theorem BookProof.NavierStokesFlow.HermiteCanonical.cre_cre_coe_add_two (x : lpFiniteModes ℕ) (k : ℕ) :
    (((cre (cre x) : lpFiniteModes ℕ) : L2I ℕ) : ℕ → ℂ) (k + 2)
      = (Real.sqrt ((k : ℝ) + 2) : ℂ) * (Real.sqrt ((k : ℝ) + 1) : ℂ)
        * ((x : L2I ℕ) : ℕ → ℂ) k := by sorry
