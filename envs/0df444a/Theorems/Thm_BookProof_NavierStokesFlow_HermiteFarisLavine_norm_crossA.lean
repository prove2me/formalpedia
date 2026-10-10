-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_HermiteFarisLavine_norm_crossA
-- name    : BookProof.NavierStokesFlow.HermiteFarisLavine.norm_crossA
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T07:26:52.565483+00:00
-- url     : https://prove2.me/theorems/3a95bd76-236d-4d1a-b12e-e4d530f47ab0
-- title:
--   `BookProof.NavierStokesFlow.HermiteFarisLavine.norm_crossA` (hκ : 0 ≤ κ) (X Y : ℕ → ℂ) (n : ℕ) : ‖crossA κ X Y n‖ = ampSeq κ X n * ‖Y (n + 2)‖
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesHermiteFarisLavine`.
--
--   `BookProof.NavierStokesFlow.HermiteFarisLavine.norm_crossA` (hκ : 0 ≤ κ) (X Y : ℕ → ℂ) (n : ℕ) : ‖crossA κ X Y n‖ = ampSeq κ X n * ‖Y (n + 2)‖
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.HermiteFarisLavine.norm_crossA`.

-- Generated from ChapterNavierStokesHermiteFarisLavine.lean — theorem BookProof.NavierStokesFlow.HermiteFarisLavine.norm_crossA
import Mathlib
import Definitions.Def_ChapterNavierStokesHermiteFarisLavine
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.HermiteFarisLavine


open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato

variable {κ : ℝ}
variable {x : maxDom (oscSymbol κ)}

theorem BookProof.NavierStokesFlow.HermiteFarisLavine.norm_crossA (hκ : 0 ≤ κ) (X Y : ℕ → ℂ) (n : ℕ) :
    ‖crossA κ X Y n‖ = ampSeq κ X n * ‖Y (n + 2)‖ := by sorry
