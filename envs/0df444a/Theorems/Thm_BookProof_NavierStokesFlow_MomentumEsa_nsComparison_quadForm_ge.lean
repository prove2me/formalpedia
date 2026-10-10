-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_MomentumEsa_nsComparison_quadForm_ge
-- name    : BookProof.NavierStokesFlow.MomentumEsa.nsComparison_quadForm_ge
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T07:54:12.336063+00:00
-- url     : https://prove2.me/theorems/2c76cf0c-1aa7-4fc6-a27a-135ade86eefa
-- title:
--   `BookProof.NavierStokesFlow.MomentumEsa.nsComparison_quadForm_ge` (d : ℕ) (p q : Fin d → ℕ → ℝ) (x : maxDom (nsSymbol d p q)) : ‖(x : L2I ℕ)‖ ^ 2 ≤ quadForm (diagMax (nsSymbol d p
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesMomentumEsa`.
--
--   `BookProof.NavierStokesFlow.MomentumEsa.nsComparison_quadForm_ge` (d : ℕ) (p q : Fin d → ℕ → ℝ) (x : maxDom (nsSymbol d p q)) : ‖(x : L2I ℕ)‖ ^ 2 ≤ quadForm (diagMax (nsSymbol d p q)) x
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.MomentumEsa.nsComparison_quadForm_ge`.

-- Generated from ChapterNavierStokesMomentumEsa.lean — theorem BookProof.NavierStokesFlow.MomentumEsa.nsComparison_quadForm_ge
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

theorem BookProof.NavierStokesFlow.MomentumEsa.nsComparison_quadForm_ge (d : ℕ) (p q : Fin d → ℕ → ℝ)
    (x : maxDom (nsSymbol d p q)) :
    ‖(x : L2I ℕ)‖ ^ 2 ≤ quadForm (diagMax (nsSymbol d p q)) x := by sorry
