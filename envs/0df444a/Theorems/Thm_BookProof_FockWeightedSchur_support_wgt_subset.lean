-- Prove2me | Theorems.Thm_BookProof_FockWeightedSchur_support_wgt_subset
-- name    : BookProof.FockWeightedSchur.support_wgt_subset
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-08T09:25:13.675223+00:00
-- url     : https://prove2.me/theorems/ce0c6599-6730-4669-bf67-4f132455420e
-- title:
--   `BookProof.FockWeightedSchur.support_wgt_subset` (u : FockAlg) : (wgt w u).support ⊆ u.support
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockWeightedSchurEsa`.
--
--   `BookProof.FockWeightedSchur.support_wgt_subset` (u : FockAlg) : (wgt w u).support ⊆ u.support
--
--   Formalization note: Lean 4 identifier `BookProof.FockWeightedSchur.support_wgt_subset`.

-- Generated from ChapterFockWeightedSchurEsa.lean — theorem BookProof.FockWeightedSchur.support_wgt_subset
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

theorem BookProof.FockWeightedSchur.support_wgt_subset (u : FockAlg) : (wgt w u).support ⊆ u.support := by sorry
