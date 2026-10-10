-- Prove2me | Theorems.Thm_BookProof_QgCouplingDGammaSum_quadForm_dGammaOp_finsetSum
-- name    : BookProof.QgCouplingDGammaSum.quadForm_dGammaOp_finsetSum
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T10:17:49.629719+00:00
-- url     : https://prove2.me/theorems/f0db5ea0-4385-4dc0-9b95-c35876eceb9a
-- title:
--   `BookProof.QgCouplingDGammaSum.quadForm_dGammaOp_finsetSum` (s : Finset ι) (cols : ι → ℕ → (ℕ →₀ ℂ)) (x : lpFiniteModes Conf) : quadForm (dGammaOp (fun k => ∑ i ∈ s, cols i k)) x =
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQgCouplingDGammaSum`.
--
--   `BookProof.QgCouplingDGammaSum.quadForm_dGammaOp_finsetSum` (s : Finset ι) (cols : ι → ℕ → (ℕ →₀ ℂ)) (x : lpFiniteModes Conf) : quadForm (dGammaOp (fun k => ∑ i ∈ s, cols i k)) x = ∑ i ∈ s, quadForm (dGammaOp (cols i)) x
--
--   Formalization note: Lean 4 identifier `BookProof.QgCouplingDGammaSum.quadForm_dGammaOp_finsetSum`.

-- Generated from ChapterQgCouplingDGammaSum.lean — theorem BookProof.QgCouplingDGammaSum.quadForm_dGammaOp_finsetSum
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterYangMillsFriedrichs
import Mathlib
import Definitions.Def_ChapterQgCouplingDGammaSum
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterNavierStokesEsa
open BookProof.FockSecondQuantization
open BookProof.QgCouplingDGammaSum



open BookProof.FockSecondQuantization
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.FriedrichsExtension BookProof.YangMillsFriedrichs

noncomputable section

variable {ι : Type*}

theorem BookProof.QgCouplingDGammaSum.quadForm_dGammaOp_finsetSum (s : Finset ι) (cols : ι → ℕ → (ℕ →₀ ℂ))
    (x : lpFiniteModes Conf) :
    quadForm (dGammaOp (fun k => ∑ i ∈ s, cols i k)) x
      = ∑ i ∈ s, quadForm (dGammaOp (cols i)) x := by sorry
