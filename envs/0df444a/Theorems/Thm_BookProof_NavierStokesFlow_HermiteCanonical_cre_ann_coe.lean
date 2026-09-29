-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_HermiteCanonical_cre_ann_coe
-- name    : BookProof.NavierStokesFlow.HermiteCanonical.cre_ann_coe
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T13:32:59.894385+00:00
-- url     : https://prove2.me/theorems/4ce37f7c-7244-4145-b6ca-b1e6239c64f9
-- title:
--   (x : lpFiniteModes ℕ) (n : ℕ) : (((cre (ann x) : lpFiniteModes ℕ) : L2I ℕ) : ℕ → ℂ) n = (n : ℂ) * ((x : L2I ℕ) : ℕ → ℂ) n
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.HermiteCanonical.cre_ann_coe` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesHermiteCanonical.lean — theorem BookProof.NavierStokesFlow.HermiteCanonical.cre_ann_coe
import Mathlib
import Definitions.Def_ChapterNavierStokesHermiteCanonical
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.HermiteCanonical







open scoped ENNReal



open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.HermiteFarisLavine

theorem BookProof.NavierStokesFlow.HermiteCanonical.cre_ann_coe (x : lpFiniteModes ℕ) (n : ℕ) :
    (((cre (ann x) : lpFiniteModes ℕ) : L2I ℕ) : ℕ → ℂ) n
      = (n : ℂ) * ((x : L2I ℕ) : ℕ → ℂ) n := by sorry
