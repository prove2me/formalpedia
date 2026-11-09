-- Prove2me | Theorems.Thm_BookProof_FockWeightedSchur_re_inner_wgt
-- name    : BookProof.FockWeightedSchur.re_inner_wgt
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-08T09:22:49.314356+00:00
-- url     : https://prove2.me/theorems/d9ceb58f-088b-481b-b242-84fb743e8d85
-- title:
--   `BookProof.FockWeightedSchur.re_inner_wgt` (u : FockAlg) : (inner ℂ (toLp u) (toLp (wgt w u)) : ℂ).re = ∑ α ∈ u.support, wSym w α * ‖u α‖ ^ 2
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockWeightedSchurEsa`.
--
--   `BookProof.FockWeightedSchur.re_inner_wgt` (u : FockAlg) : (inner ℂ (toLp u) (toLp (wgt w u)) : ℂ).re = ∑ α ∈ u.support, wSym w α * ‖u α‖ ^ 2
--
--   Formalization note: Lean 4 identifier `BookProof.FockWeightedSchur.re_inner_wgt`.

-- Generated from ChapterFockWeightedSchurEsa.lean — theorem BookProof.FockWeightedSchur.re_inner_wgt
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

theorem BookProof.FockWeightedSchur.re_inner_wgt (u : FockAlg) :
    (inner ℂ (toLp u) (toLp (wgt w u)) : ℂ).re = ∑ α ∈ u.support, wSym w α * ‖u α‖ ^ 2 := by sorry
