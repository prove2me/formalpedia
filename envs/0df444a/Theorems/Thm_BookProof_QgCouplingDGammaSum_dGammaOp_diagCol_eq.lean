-- Prove2me | Theorems.Thm_BookProof_QgCouplingDGammaSum_dGammaOp_diagCol_eq
-- name    : BookProof.QgCouplingDGammaSum.dGammaOp_diagCol_eq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T19:45:40.560292+00:00
-- url     : https://prove2.me/theorems/bf664ed7-faac-468b-ba8b-a261a5d8c04f
-- title:
--   `BookProof.QgCouplingDGammaSum.dGammaOp_diagCol_eq` (lam : ℕ → ℝ) : dGammaOp (diagCol lam) = (diagMax (occEnergy lam)).comp (Submodule.inclusion (finiteModes_le_maxDom (occEnergy l
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQgCouplingDGammaSum`.
--
--   `BookProof.QgCouplingDGammaSum.dGammaOp_diagCol_eq` (lam : ℕ → ℝ) : dGammaOp (diagCol lam) = (diagMax (occEnergy lam)).comp (Submodule.inclusion (finiteModes_le_maxDom (occEnergy lam)))
--
--   Formalization note: Lean 4 identifier `BookProof.QgCouplingDGammaSum.dGammaOp_diagCol_eq`.

-- Generated from ChapterQgCouplingDGammaSum.lean — theorem BookProof.QgCouplingDGammaSum.dGammaOp_diagCol_eq
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterYangMillsFriedrichs
import Mathlib
import Definitions.Def_ChapterQgCouplingDGammaSum
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

theorem BookProof.QgCouplingDGammaSum.dGammaOp_diagCol_eq (lam : ℕ → ℝ) :
    dGammaOp (diagCol lam)
      = (diagMax (occEnergy lam)).comp
          (Submodule.inclusion (finiteModes_le_maxDom (occEnergy lam))) := by sorry
