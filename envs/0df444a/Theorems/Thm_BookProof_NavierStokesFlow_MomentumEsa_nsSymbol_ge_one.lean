-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_MomentumEsa_nsSymbol_ge_one
-- name    : BookProof.NavierStokesFlow.MomentumEsa.nsSymbol_ge_one
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T07:54:10.716812+00:00
-- url     : https://prove2.me/theorems/3eb06544-c9b3-4681-ac86-0904ba5add3e
-- title:
--   `BookProof.NavierStokesFlow.MomentumEsa.nsSymbol_ge_one` (d : ℕ) (p q : Fin d → ℕ → ℝ) (k : ℕ) : 1 ≤ nsSymbol d p q k
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesMomentumEsa`.
--
--   `BookProof.NavierStokesFlow.MomentumEsa.nsSymbol_ge_one` (d : ℕ) (p q : Fin d → ℕ → ℝ) (k : ℕ) : 1 ≤ nsSymbol d p q k
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.MomentumEsa.nsSymbol_ge_one`.

-- Generated from ChapterNavierStokesMomentumEsa.lean — theorem BookProof.NavierStokesFlow.MomentumEsa.nsSymbol_ge_one
import Mathlib
import Definitions.Def_ChapterNavierStokesMomentumEsa
import Definitions.Def_ChapterNavierStokesGaugeY
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesGaugeY
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.MomentumEsa




open LpNat BookProof.FarisLavine IkebeKato FarisLavineLift DiagonalEsa

variable {ι : Type*}

theorem BookProof.NavierStokesFlow.MomentumEsa.nsSymbol_ge_one (d : ℕ) (p q : Fin d → ℕ → ℝ) (k : ℕ) : 1 ≤ nsSymbol d p q k := by sorry
