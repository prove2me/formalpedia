-- Prove2me | Theorems.Thm_BookProof_QgCouplingDGammaSum_dGammaOp_finsetSum_col
-- name    : BookProof.QgCouplingDGammaSum.dGammaOp_finsetSum_col
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T10:17:17.671976+00:00
-- url     : https://prove2.me/theorems/04f876ca-0077-48b3-9c54-7ea0b64ef7da
-- title:
--   `BookProof.QgCouplingDGammaSum.dGammaOp_finsetSum_col` (s : Finset ι) (cols : ι → ℕ → (ℕ →₀ ℂ)) (x : lpFiniteModes Conf) : dGammaOp (fun k => ∑ i ∈ s, cols i k) x = ∑ i ∈...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQgCouplingDGammaSum`.
--
--   `BookProof.QgCouplingDGammaSum.dGammaOp_finsetSum_col` (s : Finset ι) (cols : ι → ℕ → (ℕ →₀ ℂ)) (x : lpFiniteModes Conf) : dGammaOp (fun k => ∑ i ∈ s, cols i k) x = ∑ i ∈ s, dGammaOp (cols i) x
--
--   Formalization note: Lean 4 identifier `BookProof.QgCouplingDGammaSum.dGammaOp_finsetSum_col`.

-- Generated from ChapterQgCouplingDGammaSum.lean — theorem BookProof.QgCouplingDGammaSum.dGammaOp_finsetSum_col
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

theorem BookProof.QgCouplingDGammaSum.dGammaOp_finsetSum_col (s : Finset ι) (cols : ι → ℕ → (ℕ →₀ ℂ))
    (x : lpFiniteModes Conf) :
    dGammaOp (fun k => ∑ i ∈ s, cols i k) x = ∑ i ∈ s, dGammaOp (cols i) x := by sorry
