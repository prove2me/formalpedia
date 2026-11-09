-- Prove2me | Theorems.Thm_BookProof_FockWeightedSchur_dGamma_essentiallySelfAdjointOn_core_w
-- name    : BookProof.FockWeightedSchur.dGamma_essentiallySelfAdjointOn_core_w
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-08T09:28:03.842894+00:00
-- url     : https://prove2.me/theorems/11c73b3e-9a3d-4a72-84cd-896864792cbf
-- title:
--   `BookProof.FockWeightedSchur.dGamma_essentiallySelfAdjointOn_core_w` (hw : ∀ k, 1 ≤ w k) (hherm : IsHermCol col) (hrow : WRowBound w col K) (hcolg : WColBound w col K) (hK0 : 0 ≤ K
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockWeightedSchurEsa`.
--
--   `BookProof.FockWeightedSchur.dGamma_essentiallySelfAdjointOn_core_w` (hw : ∀ k, 1 ≤ w k) (hherm : IsHermCol col) (hrow : WRowBound w col K) (hcolg : WColBound w col K) (hK0 : 0 ≤ K) (hBg : WCommBound w col B) : EssentiallySelfAdjointOn (lpFiniteModes Conf) (dGammaOp col)
--
--   Formalization note: Lean 4 identifier `BookProof.FockWeightedSchur.dGamma_essentiallySelfAdjointOn_core_w`.

-- Generated from ChapterFockWeightedSchurEsa.lean — theorem BookProof.FockWeightedSchur.dGamma_essentiallySelfAdjointOn_core_w
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
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterNavierStokesEsa
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

theorem BookProof.FockWeightedSchur.dGamma_essentiallySelfAdjointOn_core_w (hw : ∀ k, 1 ≤ w k) (hherm : IsHermCol col)
    (hrow : WRowBound w col K) (hcolg : WColBound w col K) (hK0 : 0 ≤ K)
    (hBg : WCommBound w col B) :
    EssentiallySelfAdjointOn (lpFiniteModes Conf) (dGammaOp col) := by sorry
