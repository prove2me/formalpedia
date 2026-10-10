-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_MomentumEsa_nsSymbol_nonneg
-- name    : BookProof.NavierStokesFlow.MomentumEsa.nsSymbol_nonneg
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T07:50:46.885699+00:00
-- url     : https://prove2.me/theorems/0c6631c8-9803-4e43-9998-4b08dd37ea31
-- title:
--   `BookProof.NavierStokesFlow.MomentumEsa.nsSymbol_nonneg` (d : ℕ) (p q : Fin d → ℕ → ℝ) (k : ℕ) : 0 ≤ nsSymbol d p q k
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesMomentumEsa`.
--
--   `BookProof.NavierStokesFlow.MomentumEsa.nsSymbol_nonneg` (d : ℕ) (p q : Fin d → ℕ → ℝ) (k : ℕ) : 0 ≤ nsSymbol d p q k
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.MomentumEsa.nsSymbol_nonneg`.

-- Generated from ChapterNavierStokesMomentumEsa.lean — theorem BookProof.NavierStokesFlow.MomentumEsa.nsSymbol_nonneg
import Mathlib
import Definitions.Def_ChapterNavierStokesMomentumEsa
import Definitions.Def_ChapterNavierStokesGaugeY
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesGaugeY
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.MomentumEsa




open LpNat BookProof.FarisLavine IkebeKato FarisLavineLift DiagonalEsa

variable {ι : Type*}

theorem BookProof.NavierStokesFlow.MomentumEsa.nsSymbol_nonneg (d : ℕ) (p q : Fin d → ℕ → ℝ) (k : ℕ) : 0 ≤ nsSymbol d p q k := by sorry
