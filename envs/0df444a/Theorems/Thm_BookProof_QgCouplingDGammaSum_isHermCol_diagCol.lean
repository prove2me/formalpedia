-- Prove2me | Theorems.Thm_BookProof_QgCouplingDGammaSum_isHermCol_diagCol
-- name    : BookProof.QgCouplingDGammaSum.isHermCol_diagCol
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T10:19:45.755988+00:00
-- url     : https://prove2.me/theorems/ce587164-1d9d-41ce-aa65-9c50be0ab948
-- title:
--   `BookProof.QgCouplingDGammaSum.isHermCol_diagCol` (lam : ℕ → ℝ) : IsHermCol (diagCol lam)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQgCouplingDGammaSum`.
--
--   `BookProof.QgCouplingDGammaSum.isHermCol_diagCol` (lam : ℕ → ℝ) : IsHermCol (diagCol lam)
--
--   Formalization note: Lean 4 identifier `BookProof.QgCouplingDGammaSum.isHermCol_diagCol`.

-- Generated from ChapterQgCouplingDGammaSum.lean — theorem BookProof.QgCouplingDGammaSum.isHermCol_diagCol
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

theorem BookProof.QgCouplingDGammaSum.isHermCol_diagCol (lam : ℕ → ℝ) : IsHermCol (diagCol lam) := by sorry
