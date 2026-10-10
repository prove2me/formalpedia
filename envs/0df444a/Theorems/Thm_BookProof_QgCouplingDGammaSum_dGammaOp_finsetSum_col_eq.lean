-- Prove2me | Theorems.Thm_BookProof_QgCouplingDGammaSum_dGammaOp_finsetSum_col_eq
-- name    : BookProof.QgCouplingDGammaSum.dGammaOp_finsetSum_col_eq
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T10:17:28.216387+00:00
-- url     : https://prove2.me/theorems/ea407a74-b284-4843-9749-74810768fd81
-- title:
--   `BookProof.QgCouplingDGammaSum.dGammaOp_finsetSum_col_eq` (s : Finset ι) (cols : ι → ℕ → (ℕ →₀ ℂ)) : dGammaOp (fun k => ∑ i ∈ s, cols i k) = ∑ i ∈ s, dGammaOp (cols i)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQgCouplingDGammaSum`.
--
--   `BookProof.QgCouplingDGammaSum.dGammaOp_finsetSum_col_eq` (s : Finset ι) (cols : ι → ℕ → (ℕ →₀ ℂ)) : dGammaOp (fun k => ∑ i ∈ s, cols i k) = ∑ i ∈ s, dGammaOp (cols i)
--
--   Formalization note: Lean 4 identifier `BookProof.QgCouplingDGammaSum.dGammaOp_finsetSum_col_eq`.

-- Generated from ChapterQgCouplingDGammaSum.lean — theorem BookProof.QgCouplingDGammaSum.dGammaOp_finsetSum_col_eq
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

theorem BookProof.QgCouplingDGammaSum.dGammaOp_finsetSum_col_eq (s : Finset ι) (cols : ι → ℕ → (ℕ →₀ ℂ)) :
    dGammaOp (fun k => ∑ i ∈ s, cols i k) = ∑ i ∈ s, dGammaOp (cols i) := by sorry
