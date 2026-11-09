-- Prove2me | Theorems.Thm_BookProof_FockWeightedSchur_wdeg_eq_sum
-- name    : BookProof.FockWeightedSchur.wdeg_eq_sum
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-08T09:21:58.470149+00:00
-- url     : https://prove2.me/theorems/d3d30489-63a1-4c78-9868-be3023b56c93
-- title:
--   `BookProof.FockWeightedSchur.wdeg_eq_sum` {α : Conf} {S : Finset ℕ} (h : α.support ⊆ S) : wdeg w α = ∑ k ∈ S, w k ^ 2 * α k
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockWeightedSchurEsa`.
--
--   `BookProof.FockWeightedSchur.wdeg_eq_sum` {α : Conf} {S : Finset ℕ} (h : α.support ⊆ S) : wdeg w α = ∑ k ∈ S, w k ^ 2 * α k
--
--   Formalization note: Lean 4 identifier `BookProof.FockWeightedSchur.wdeg_eq_sum`.

-- Generated from ChapterFockWeightedSchurEsa.lean — theorem BookProof.FockWeightedSchur.wdeg_eq_sum
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

theorem BookProof.FockWeightedSchur.wdeg_eq_sum {α : Conf} {S : Finset ℕ} (h : α.support ⊆ S) :
    wdeg w α = ∑ k ∈ S, w k ^ 2 * α k := by sorry
