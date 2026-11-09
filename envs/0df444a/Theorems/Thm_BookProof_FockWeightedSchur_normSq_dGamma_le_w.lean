-- Prove2me | Theorems.Thm_BookProof_FockWeightedSchur_normSq_dGamma_le_w
-- name    : BookProof.FockWeightedSchur.normSq_dGamma_le_w
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-08T09:26:32.573862+00:00
-- url     : https://prove2.me/theorems/63822a54-5d35-462b-a3e4-15fe4306e9c1
-- title:
--   `BookProof.FockWeightedSchur.normSq_dGamma_le_w` (hw : ∀ k, 1 ≤ w k) (hherm : IsHermCol col) (hrow : WRowBound w col K) (hcolg : WColBound w col K) (hK0 : 0 ≤ K) (u : FockAlg) : ‖t
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockWeightedSchurEsa`.
--
--   `BookProof.FockWeightedSchur.normSq_dGamma_le_w` (hw : ∀ k, 1 ≤ w k) (hherm : IsHermCol col) (hrow : WRowBound w col K) (hcolg : WColBound w col K) (hK0 : 0 ≤ K) (u : FockAlg) : ‖toLp (dGamma col u)‖ ^ 2 ≤ K ^ 2 * ∑ α ∈ u.support, wSym w α ^ 2 * ‖u α‖ ^ 2
--
--   Formalization note: Lean 4 identifier `BookProof.FockWeightedSchur.normSq_dGamma_le_w`.

-- Generated from ChapterFockWeightedSchurEsa.lean — theorem BookProof.FockWeightedSchur.normSq_dGamma_le_w
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
variable {col : ℕ → (ℕ →₀ ℂ)} {K B : ℝ}

theorem BookProof.FockWeightedSchur.normSq_dGamma_le_w (hw : ∀ k, 1 ≤ w k) (hherm : IsHermCol col)
    (hrow : WRowBound w col K) (hcolg : WColBound w col K) (hK0 : 0 ≤ K) (u : FockAlg) :
    ‖toLp (dGamma col u)‖ ^ 2 ≤ K ^ 2 * ∑ α ∈ u.support, wSym w α ^ 2 * ‖u α‖ ^ 2 := by sorry
