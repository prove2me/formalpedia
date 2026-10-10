-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_HermiteFarisLavine_amp_le_symbol
-- name    : BookProof.NavierStokesFlow.HermiteFarisLavine.amp_le_symbol
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T07:27:12.15699+00:00
-- url     : https://prove2.me/theorems/fdcd84a4-4bc7-4448-a627-d2c9cf52ea5b
-- title:
--   `BookProof.NavierStokesFlow.HermiteFarisLavine.amp_le_symbol` (hκ : 0 ≤ κ) (n : ℕ) : amp κ n ≤ (1 / 4 + κ / 2) * oscSymbol κ n
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesHermiteFarisLavine`.
--
--   `BookProof.NavierStokesFlow.HermiteFarisLavine.amp_le_symbol` (hκ : 0 ≤ κ) (n : ℕ) : amp κ n ≤ (1 / 4 + κ / 2) * oscSymbol κ n
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.HermiteFarisLavine.amp_le_symbol`.

-- Generated from ChapterNavierStokesHermiteFarisLavine.lean — theorem BookProof.NavierStokesFlow.HermiteFarisLavine.amp_le_symbol
import Mathlib
import Definitions.Def_ChapterNavierStokesHermiteFarisLavine
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.HermiteFarisLavine


open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato

variable {κ : ℝ}

theorem BookProof.NavierStokesFlow.HermiteFarisLavine.amp_le_symbol (hκ : 0 ≤ κ) (n : ℕ) :
    amp κ n ≤ (1 / 4 + κ / 2) * oscSymbol κ n := by sorry
