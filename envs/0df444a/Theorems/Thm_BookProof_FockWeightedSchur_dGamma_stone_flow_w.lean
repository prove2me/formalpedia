-- Prove2me | Theorems.Thm_BookProof_FockWeightedSchur_dGamma_stone_flow_w
-- name    : BookProof.FockWeightedSchur.dGamma_stone_flow_w
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-08T09:28:39.129311+00:00
-- url     : https://prove2.me/theorems/a87df608-d96f-47b6-a0a1-23605461519a
-- title:
--   `BookProof.FockWeightedSchur.dGamma_stone_flow_w` (hw : ∀ k, 1 ≤ w k) (hherm : IsHermCol col) (hrow : WRowBound w col K) (hcolg : WColBound w col K) (hK0 : 0 ≤ K) (hBg : WCommBound
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockWeightedSchurEsa`.
--
--   `BookProof.FockWeightedSchur.dGamma_stone_flow_w` (hw : ∀ k, 1 ≤ w k) (hherm : IsHermCol col) (hrow : WRowBound w col K) (hcolg : WColBound w col K) (hK0 : 0 ≤ K) (hBg : WCommBound w col B) : ∃ (T : UnboundedSelfAdjoint Fock) (U : ℝ → (Fock →L[ℂ] Fock)), IsSelfAdjointExtension (dGammaOp col) T.op ∧ IsStoneFlow T U
--
--   Formalization note: Lean 4 identifier `BookProof.FockWeightedSchur.dGamma_stone_flow_w`.

-- Generated from ChapterFockWeightedSchurEsa.lean — theorem BookProof.FockWeightedSchur.dGamma_stone_flow_w
import Definitions.Def_ChapterCoreBoundsEsa
import Definitions.Def_ChapterFockSchurEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterFockWeightedSchurEsaPromoted
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterStoneResolvent
import Definitions.Def_ChapterFockWeightedSchurEsaPromoted
import Definitions.Def_ChapterShiftedQuadraticEsa
import Definitions.Def_ChapterSirkBandLedger
open BookProof.EsaClosure
open BookProof.FockSecondQuantization
open BookProof.StoneBridge
open BookProof.FockWeightedSchur



open BookProof.FockSecondQuantization BookProof.CoreBounds BookProof.FockSchur
open BookProof.FarisLavine BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {w : ℕ → ℝ}
variable {col : ℕ → (ℕ →₀ ℂ)} {K B : ℝ}

theorem BookProof.FockWeightedSchur.dGamma_stone_flow_w (hw : ∀ k, 1 ≤ w k) (hherm : IsHermCol col)
    (hrow : WRowBound w col K) (hcolg : WColBound w col K) (hK0 : 0 ≤ K)
    (hBg : WCommBound w col B) :
    ∃ (T : UnboundedSelfAdjoint Fock) (U : ℝ → (Fock →L[ℂ] Fock)),
      IsSelfAdjointExtension (dGammaOp col) T.op ∧ IsStoneFlow T U := by sorry
