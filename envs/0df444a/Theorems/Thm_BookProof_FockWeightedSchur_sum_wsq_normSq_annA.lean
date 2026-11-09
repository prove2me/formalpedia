-- Prove2me | Theorems.Thm_BookProof_FockWeightedSchur_sum_wsq_normSq_annA
-- name    : BookProof.FockWeightedSchur.sum_wsq_normSq_annA
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-08T09:22:15.408465+00:00
-- url     : https://prove2.me/theorems/ec59c834-16c7-45cc-827a-9b11940a2e43
-- title:
--   `BookProof.FockWeightedSchur.sum_wsq_normSq_annA` {u : FockAlg} {L : Finset ℕ} (hL : modes u ⊆ L) : ∑ k ∈ L, w k ^ 2 * ‖toLp (annA k u)‖ ^ 2 = ∑ α ∈ u.support, wdeg w α * ‖u...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockWeightedSchurEsa`.
--
--   `BookProof.FockWeightedSchur.sum_wsq_normSq_annA` {u : FockAlg} {L : Finset ℕ} (hL : modes u ⊆ L) : ∑ k ∈ L, w k ^ 2 * ‖toLp (annA k u)‖ ^ 2 = ∑ α ∈ u.support, wdeg w α * ‖u α‖ ^ 2
--
--   Formalization note: Lean 4 identifier `BookProof.FockWeightedSchur.sum_wsq_normSq_annA`.

-- Generated from ChapterFockWeightedSchurEsa.lean — theorem BookProof.FockWeightedSchur.sum_wsq_normSq_annA
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

theorem BookProof.FockWeightedSchur.sum_wsq_normSq_annA {u : FockAlg} {L : Finset ℕ} (hL : modes u ⊆ L) :
    ∑ k ∈ L, w k ^ 2 * ‖toLp (annA k u)‖ ^ 2 = ∑ α ∈ u.support, wdeg w α * ‖u α‖ ^ 2 := by sorry
