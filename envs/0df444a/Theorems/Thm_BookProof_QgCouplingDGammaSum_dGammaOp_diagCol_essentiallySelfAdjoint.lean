-- Prove2me | Theorems.Thm_BookProof_QgCouplingDGammaSum_dGammaOp_diagCol_essentiallySelfAdjoint
-- name    : BookProof.QgCouplingDGammaSum.dGammaOp_diagCol_essentiallySelfAdjoint
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T22:57:29.237978+00:00
-- url     : https://prove2.me/theorems/aa0ab06b-61aa-4ad2-944c-f2ab62aa4813
-- title:
--   `BookProof.QgCouplingDGammaSum.dGammaOp_diagCol_essentiallySelfAdjoint` {lam : ℕ → ℝ} (hlam : ∀ k, 0 ≤ lam k) : EssentiallySelfAdjointOn (lpFiniteModes Conf) (dGammaOp (diagCol lam
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQgCouplingDGammaSum`.
--
--   `BookProof.QgCouplingDGammaSum.dGammaOp_diagCol_essentiallySelfAdjoint` {lam : ℕ → ℝ} (hlam : ∀ k, 0 ≤ lam k) : EssentiallySelfAdjointOn (lpFiniteModes Conf) (dGammaOp (diagCol lam))
--
--   Formalization note: Lean 4 identifier `BookProof.QgCouplingDGammaSum.dGammaOp_diagCol_essentiallySelfAdjoint`.

-- Generated from ChapterQgCouplingDGammaSum.lean — theorem BookProof.QgCouplingDGammaSum.dGammaOp_diagCol_essentiallySelfAdjoint
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterYangMillsFriedrichs
import Mathlib
import Definitions.Def_ChapterQgCouplingDGammaSum
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
open BookProof.FockOneParticleGap
open BookProof.FockSecondQuantization
open BookProof.NavierStokesFlow.IkebeKato
open BookProof.QgCouplingDGammaSum



open BookProof.FockSecondQuantization
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.FriedrichsExtension BookProof.YangMillsFriedrichs

noncomputable section

variable {ι : Type*}

theorem BookProof.QgCouplingDGammaSum.dGammaOp_diagCol_essentiallySelfAdjoint {lam : ℕ → ℝ} (hlam : ∀ k, 0 ≤ lam k) :
    EssentiallySelfAdjointOn (lpFiniteModes Conf) (dGammaOp (diagCol lam)) := by sorry
