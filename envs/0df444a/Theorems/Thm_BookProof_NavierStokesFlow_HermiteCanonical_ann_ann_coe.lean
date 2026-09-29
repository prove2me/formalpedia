-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_HermiteCanonical_ann_ann_coe
-- name    : BookProof.NavierStokesFlow.HermiteCanonical.ann_ann_coe
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T13:27:00.540859+00:00
-- url     : https://prove2.me/theorems/07472283-4807-4e4d-a54a-36cce45b4f43
-- title:
--   (x : lpFiniteModes ℕ) (n : ℕ) : (((ann (ann x) : lpFiniteModes ℕ) : L2I ℕ) : ℕ → ℂ) n = (Real.sqrt ((n : ℝ) + 1) : ℂ) * (Real.sqrt ((n : ℝ) + 2) : ℂ) * ((x : L2I ℕ) : ℕ → ℂ) (n + 2)
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.HermiteCanonical.ann_ann_coe` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesHermiteCanonical.lean — theorem BookProof.NavierStokesFlow.HermiteCanonical.ann_ann_coe
import Mathlib
import Definitions.Def_ChapterNavierStokesHermiteCanonical
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.HermiteCanonical







open scoped ENNReal



open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.HermiteFarisLavine

theorem BookProof.NavierStokesFlow.HermiteCanonical.ann_ann_coe (x : lpFiniteModes ℕ) (n : ℕ) :
    (((ann (ann x) : lpFiniteModes ℕ) : L2I ℕ) : ℕ → ℂ) n
      = (Real.sqrt ((n : ℝ) + 1) : ℂ) * (Real.sqrt ((n : ℝ) + 2) : ℂ)
        * ((x : L2I ℕ) : ℕ → ℂ) (n + 2) := by sorry
