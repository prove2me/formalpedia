-- Prove2me | Theorems.Thm_BookProof_QgCouplingDGammaSum_dGamma_diagCol_apply
-- name    : BookProof.QgCouplingDGammaSum.dGamma_diagCol_apply
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T10:18:35.689968+00:00
-- url     : https://prove2.me/theorems/04d3b8f1-ade5-4767-83fe-c5d23e2510d3
-- title:
--   `BookProof.QgCouplingDGammaSum.dGamma_diagCol_apply` (lam : ℕ → ℝ) (u : FockAlg) (α : Conf) : dGamma (diagCol lam) u α = ((occEnergy lam α : ℝ) : ℂ) * u α
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQgCouplingDGammaSum`.
--
--   `BookProof.QgCouplingDGammaSum.dGamma_diagCol_apply` (lam : ℕ → ℝ) (u : FockAlg) (α : Conf) : dGamma (diagCol lam) u α = ((occEnergy lam α : ℝ) : ℂ) * u α
--
--   Formalization note: Lean 4 identifier `BookProof.QgCouplingDGammaSum.dGamma_diagCol_apply`.

-- Generated from ChapterQgCouplingDGammaSum.lean — theorem BookProof.QgCouplingDGammaSum.dGamma_diagCol_apply
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

theorem BookProof.QgCouplingDGammaSum.dGamma_diagCol_apply (lam : ℕ → ℝ) (u : FockAlg) (α : Conf) :
    dGamma (diagCol lam) u α = ((occEnergy lam α : ℝ) : ℂ) * u α := by sorry
