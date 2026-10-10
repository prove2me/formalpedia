-- Prove2me | Theorems.Thm_BookProof_QgCouplingDGammaSum_creA_annA_apply
-- name    : BookProof.QgCouplingDGammaSum.creA_annA_apply
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T10:18:39.345564+00:00
-- url     : https://prove2.me/theorems/bfe3c822-ebaa-4e13-878c-74341f196a85
-- title:
--   `BookProof.QgCouplingDGammaSum.creA_annA_apply` (k : ℕ) (u : FockAlg) (α : Conf) : creA k (annA k u) α = ((α k : ℝ) : ℂ) * u α
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQgCouplingDGammaSum`.
--
--   `BookProof.QgCouplingDGammaSum.creA_annA_apply` (k : ℕ) (u : FockAlg) (α : Conf) : creA k (annA k u) α = ((α k : ℝ) : ℂ) * u α
--
--   Formalization note: Lean 4 identifier `BookProof.QgCouplingDGammaSum.creA_annA_apply`.

-- Generated from ChapterQgCouplingDGammaSum.lean — theorem BookProof.QgCouplingDGammaSum.creA_annA_apply
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterYangMillsFriedrichs
import Mathlib
import Definitions.Def_ChapterQgCouplingDGammaSum
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterNavierStokesFockCanonical
open BookProof.FockSecondQuantization
open BookProof.NavierStokesFlow.FockCanonical
open BookProof.QgCouplingDGammaSum



open BookProof.FockSecondQuantization
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.FriedrichsExtension BookProof.YangMillsFriedrichs

noncomputable section

variable {ι : Type*}

theorem BookProof.QgCouplingDGammaSum.creA_annA_apply (k : ℕ) (u : FockAlg) (α : Conf) :
    creA k (annA k u) α = ((α k : ℝ) : ℂ) * u α := by sorry
