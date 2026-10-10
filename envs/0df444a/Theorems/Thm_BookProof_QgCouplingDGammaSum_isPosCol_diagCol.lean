-- Prove2me | Theorems.Thm_BookProof_QgCouplingDGammaSum_isPosCol_diagCol
-- name    : BookProof.QgCouplingDGammaSum.isPosCol_diagCol
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T10:20:27.751441+00:00
-- url     : https://prove2.me/theorems/27f23b88-b8ce-4149-8fb9-3c59e4cf5111
-- title:
--   `BookProof.QgCouplingDGammaSum.isPosCol_diagCol` {lam : ℕ → ℝ} (hlam : ∀ k, 0 ≤ lam k) : IsPosCol (diagCol lam)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQgCouplingDGammaSum`.
--
--   `BookProof.QgCouplingDGammaSum.isPosCol_diagCol` {lam : ℕ → ℝ} (hlam : ∀ k, 0 ≤ lam k) : IsPosCol (diagCol lam)
--
--   Formalization note: Lean 4 identifier `BookProof.QgCouplingDGammaSum.isPosCol_diagCol`.

-- Generated from ChapterQgCouplingDGammaSum.lean — theorem BookProof.QgCouplingDGammaSum.isPosCol_diagCol
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterYangMillsFriedrichs
import Mathlib
import Definitions.Def_ChapterQgCouplingDGammaSum
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockSecondQuantization
open BookProof.FockOneParticleGap
open BookProof.FockSecondQuantization
open BookProof.QgCouplingDGammaSum



open BookProof.FockSecondQuantization
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.FriedrichsExtension BookProof.YangMillsFriedrichs

noncomputable section

variable {ι : Type*}

theorem BookProof.QgCouplingDGammaSum.isPosCol_diagCol {lam : ℕ → ℝ} (hlam : ∀ k, 0 ≤ lam k) : IsPosCol (diagCol lam) := by sorry
