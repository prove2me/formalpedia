-- Prove2me | Theorems.Thm_BookProof_QgCouplingDGammaSum_creVec_single
-- name    : BookProof.QgCouplingDGammaSum.creVec_single
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T10:18:13.697972+00:00
-- url     : https://prove2.me/theorems/ed8e6eda-f9f1-4776-9f40-8230065d067d
-- title:
--   `BookProof.QgCouplingDGammaSum.creVec_single` (k : ℕ) (z : ℂ) (x : FockAlg) : creVec (Finsupp.single k z) x = z • creA k x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQgCouplingDGammaSum`.
--
--   `BookProof.QgCouplingDGammaSum.creVec_single` (k : ℕ) (z : ℂ) (x : FockAlg) : creVec (Finsupp.single k z) x = z • creA k x
--
--   Formalization note: Lean 4 identifier `BookProof.QgCouplingDGammaSum.creVec_single`.

-- Generated from ChapterQgCouplingDGammaSum.lean — theorem BookProof.QgCouplingDGammaSum.creVec_single
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterYangMillsFriedrichs
import Mathlib
import Definitions.Def_ChapterQgCouplingDGammaSum
import Definitions.Def_ChapterFockSecondQuantization
open BookProof.FockSecondQuantization
open BookProof.QgCouplingDGammaSum



open BookProof.FockSecondQuantization
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.FriedrichsExtension BookProof.YangMillsFriedrichs

noncomputable section

variable {ι : Type*}

theorem BookProof.QgCouplingDGammaSum.creVec_single (k : ℕ) (z : ℂ) (x : FockAlg) :
    creVec (Finsupp.single k z) x = z • creA k x := by sorry
