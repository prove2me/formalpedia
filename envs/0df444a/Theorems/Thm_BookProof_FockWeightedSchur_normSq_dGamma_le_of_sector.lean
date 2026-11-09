-- Prove2me | Theorems.Thm_BookProof_FockWeightedSchur_normSq_dGamma_le_of_sector
-- name    : BookProof.FockWeightedSchur.normSq_dGamma_le_of_sector
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-08T09:25:23.28667+00:00
-- url     : https://prove2.me/theorems/21e721b7-94b3-452d-ad70-1184003a4f2a
-- title:
--   `BookProof.FockWeightedSchur.normSq_dGamma_le_of_sector` (hw : ∀ k, 1 ≤ w k) (hherm : IsHermCol col) (hrow : WRowBound w col K) (hcolg : WColBound w col K) (hK0 : 0 ≤ K) {n : ℕ} {u
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockWeightedSchurEsa`.
--
--   `BookProof.FockWeightedSchur.normSq_dGamma_le_of_sector` (hw : ∀ k, 1 ≤ w k) (hherm : IsHermCol col) (hrow : WRowBound w col K) (hcolg : WColBound w col K) (hK0 : 0 ≤ K) {n : ℕ} {u : FockAlg} (hu : InSector n u) : ‖toLp (dGamma col u)‖ ^ 2 ≤ K ^ 2 * ((n : ℝ) * ∑ α ∈ u.support, wdeg w α * ‖u α‖ ^ 2)
--
--   Formalization note: Lean 4 identifier `BookProof.FockWeightedSchur.normSq_dGamma_le_of_sector`.

-- Generated from ChapterFockWeightedSchurEsa.lean — theorem BookProof.FockWeightedSchur.normSq_dGamma_le_of_sector
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

theorem BookProof.FockWeightedSchur.normSq_dGamma_le_of_sector (hw : ∀ k, 1 ≤ w k) (hherm : IsHermCol col)
    (hrow : WRowBound w col K) (hcolg : WColBound w col K) (hK0 : 0 ≤ K)
    {n : ℕ} {u : FockAlg} (hu : InSector n u) :
    ‖toLp (dGamma col u)‖ ^ 2 ≤ K ^ 2 * ((n : ℝ) * ∑ α ∈ u.support, wdeg w α * ‖u α‖ ^ 2) := by sorry
