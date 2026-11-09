-- Prove2me | Theorems.Thm_BookProof_FockWeightedSchur_inner_wgt_symm
-- name    : BookProof.FockWeightedSchur.inner_wgt_symm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-08T09:24:29.697205+00:00
-- url     : https://prove2.me/theorems/276eb202-d3ca-4609-826b-01ce0e339cf1
-- title:
--   `BookProof.FockWeightedSchur.inner_wgt_symm` (u v : FockAlg) : (inner ℂ (toLp (wgt w u)) (toLp v) : ℂ) = inner ℂ (toLp u) (toLp (wgt w v))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockWeightedSchurEsa`.
--
--   `BookProof.FockWeightedSchur.inner_wgt_symm` (u v : FockAlg) : (inner ℂ (toLp (wgt w u)) (toLp v) : ℂ) = inner ℂ (toLp u) (toLp (wgt w v))
--
--   Formalization note: Lean 4 identifier `BookProof.FockWeightedSchur.inner_wgt_symm`.

-- Generated from ChapterFockWeightedSchurEsa.lean — theorem BookProof.FockWeightedSchur.inner_wgt_symm
import Definitions.Def_ChapterCoreBoundsEsa
import Definitions.Def_ChapterFockSchurEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterFockWeightedSchurEsaPromoted
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterFockWeightedSchurEsaPromoted
import Definitions.Def_ChapterSirkBandLedger
open BookProof.FockSecondQuantization
open BookProof.FockWeightedSchur



open BookProof.FockSecondQuantization BookProof.CoreBounds BookProof.FockSchur
open BookProof.FarisLavine BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {w : ℕ → ℝ}

theorem BookProof.FockWeightedSchur.inner_wgt_symm (u v : FockAlg) :
    (inner ℂ (toLp (wgt w u)) (toLp v) : ℂ) = inner ℂ (toLp u) (toLp (wgt w v)) := by sorry
