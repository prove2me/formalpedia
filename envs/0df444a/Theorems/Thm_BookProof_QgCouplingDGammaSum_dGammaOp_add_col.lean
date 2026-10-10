-- Prove2me | Theorems.Thm_BookProof_QgCouplingDGammaSum_dGammaOp_add_col
-- name    : BookProof.QgCouplingDGammaSum.dGammaOp_add_col
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T10:19:51.79298+00:00
-- url     : https://prove2.me/theorems/7de4ce31-2fa7-4f63-b63e-802c7fb5b982
-- title:
--   `BookProof.QgCouplingDGammaSum.dGammaOp_add_col` (a b : ℕ → (ℕ →₀ ℂ)) (x : lpFiniteModes Conf) : dGammaOp (fun k => a k + b k) x = dGammaOp a x + dGammaOp b x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQgCouplingDGammaSum`.
--
--   `BookProof.QgCouplingDGammaSum.dGammaOp_add_col` (a b : ℕ → (ℕ →₀ ℂ)) (x : lpFiniteModes Conf) : dGammaOp (fun k => a k + b k) x = dGammaOp a x + dGammaOp b x
--
--   Formalization note: Lean 4 identifier `BookProof.QgCouplingDGammaSum.dGammaOp_add_col`.

-- Generated from ChapterQgCouplingDGammaSum.lean — theorem BookProof.QgCouplingDGammaSum.dGammaOp_add_col
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterYangMillsFriedrichs
import Mathlib
import Definitions.Def_ChapterQgCouplingDGammaSum
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterNavierStokesEsa
open BookProof.FockSecondQuantization
open BookProof.QgCouplingDGammaSum



open BookProof.FockSecondQuantization
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.FriedrichsExtension BookProof.YangMillsFriedrichs

noncomputable section

variable {ι : Type*}

theorem BookProof.QgCouplingDGammaSum.dGammaOp_add_col (a b : ℕ → (ℕ →₀ ℂ)) (x : lpFiniteModes Conf) :
    dGammaOp (fun k => a k + b k) x = dGammaOp a x + dGammaOp b x := by sorry
