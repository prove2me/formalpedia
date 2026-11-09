-- Prove2me | Theorems.Thm_BookProof_FockWeightedSchur_dGammaOp_coreRelBound_w
-- name    : BookProof.FockWeightedSchur.dGammaOp_coreRelBound_w
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-08T10:19:28.966671+00:00
-- url     : https://prove2.me/theorems/03d8b18a-8160-4a33-8dbc-ab71380069c5
-- title:
--   `BookProof.FockWeightedSchur.dGammaOp_coreRelBound_w` (hw : ∀ k, 1 ≤ w k) (hherm : IsHermCol col) (hrow : WRowBound w col K) (hcolg : WColBound w col K) (hK0 : 0 ≤ K) : CoreRelBoun
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockWeightedSchurEsa`.
--
--   `BookProof.FockWeightedSchur.dGammaOp_coreRelBound_w` (hw : ∀ k, 1 ≤ w k) (hherm : IsHermCol col) (hrow : WRowBound w col K) (hcolg : WColBound w col K) (hK0 : 0 ≤ K) : CoreRelBound (wSym w) (dGammaOp col) K
--
--   Formalization note: Lean 4 identifier `BookProof.FockWeightedSchur.dGammaOp_coreRelBound_w`.

-- Generated from ChapterFockWeightedSchurEsa.lean — theorem BookProof.FockWeightedSchur.dGammaOp_coreRelBound_w
import Definitions.Def_ChapterCoreBoundsEsa
import Definitions.Def_ChapterFockSchurEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterFockWeightedSchurEsaPromoted
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterFockWeightedSchurEsaPromoted
import Definitions.Def_ChapterSirkBandLedger
open BookProof.FockSecondQuantization
open BookProof.NavierStokesFlow.IkebeKato
open BookProof.FockWeightedSchur



open BookProof.FockSecondQuantization BookProof.CoreBounds BookProof.FockSchur
open BookProof.FarisLavine BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {w : ℕ → ℝ}
variable {col : ℕ → (ℕ →₀ ℂ)} {K B : ℝ}

theorem BookProof.FockWeightedSchur.dGammaOp_coreRelBound_w (hw : ∀ k, 1 ≤ w k) (hherm : IsHermCol col)
    (hrow : WRowBound w col K) (hcolg : WColBound w col K) (hK0 : 0 ≤ K) :
    CoreRelBound (wSym w) (dGammaOp col) K := by sorry
