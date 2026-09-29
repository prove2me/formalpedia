-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_HermiteCanonical_ann_coe
-- name    : BookProof.NavierStokesFlow.HermiteCanonical.ann_coe
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T11:29:27.715056+00:00
-- url     : https://prove2.me/theorems/c0c02d7e-adc3-454b-8345-788702a52c5b
-- title:
--   (x : lpFiniteModes ℕ) (n : ℕ) : (((ann x : lpFiniteModes ℕ) : L2I ℕ) : ℕ → ℂ) n = (Real.sqrt (n + 1) : ℂ) * ((x : L2I ℕ) : ℕ → ℂ) (n + 1)
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.HermiteCanonical.ann_coe` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesHermiteCanonical.lean — theorem BookProof.NavierStokesFlow.HermiteCanonical.ann_coe
import Mathlib
import Definitions.Def_ChapterNavierStokesHermiteCanonical
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.HermiteCanonical







open scoped ENNReal



open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.HermiteFarisLavine

theorem BookProof.NavierStokesFlow.HermiteCanonical.ann_coe (x : lpFiniteModes ℕ) (n : ℕ) :
    (((ann x : lpFiniteModes ℕ) : L2I ℕ) : ℕ → ℂ) n
      = (Real.sqrt (n + 1) : ℂ) * ((x : L2I ℕ) : ℕ → ℂ) (n + 1) := by sorry
