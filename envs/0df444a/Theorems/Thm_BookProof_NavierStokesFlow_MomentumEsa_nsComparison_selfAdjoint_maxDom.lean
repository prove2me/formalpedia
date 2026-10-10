-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_MomentumEsa_nsComparison_selfAdjoint_maxDom
-- name    : BookProof.NavierStokesFlow.MomentumEsa.nsComparison_selfAdjoint_maxDom
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T07:52:15.530348+00:00
-- url     : https://prove2.me/theorems/5d532d09-0f65-4b5c-a2c2-ef781c69426e
-- title:
--   `BookProof.NavierStokesFlow.MomentumEsa.nsComparison_selfAdjoint_maxDom` (d : ℕ) (p q : Fin d → ℕ → ℝ) : EssentiallySelfAdjointOn (maxDom (nsSymbol d p q)) (diagMax (nsSymbol d p q
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesMomentumEsa`.
--
--   `BookProof.NavierStokesFlow.MomentumEsa.nsComparison_selfAdjoint_maxDom` (d : ℕ) (p q : Fin d → ℕ → ℝ) : EssentiallySelfAdjointOn (maxDom (nsSymbol d p q)) (diagMax (nsSymbol d p q))
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.MomentumEsa.nsComparison_selfAdjoint_maxDom`.

-- Generated from ChapterNavierStokesMomentumEsa.lean — theorem BookProof.NavierStokesFlow.MomentumEsa.nsComparison_selfAdjoint_maxDom
import Mathlib
import Definitions.Def_ChapterNavierStokesMomentumEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterNavierStokesGaugeY
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesGaugeY
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.MomentumEsa




open LpNat BookProof.FarisLavine IkebeKato FarisLavineLift DiagonalEsa

variable {ι : Type*}

theorem BookProof.NavierStokesFlow.MomentumEsa.nsComparison_selfAdjoint_maxDom (d : ℕ) (p q : Fin d → ℕ → ℝ) :
    EssentiallySelfAdjointOn (maxDom (nsSymbol d p q)) (diagMax (nsSymbol d p q)) := by sorry
