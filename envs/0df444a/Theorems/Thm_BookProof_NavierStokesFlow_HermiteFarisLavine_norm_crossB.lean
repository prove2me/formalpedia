-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_HermiteFarisLavine_norm_crossB
-- name    : BookProof.NavierStokesFlow.HermiteFarisLavine.norm_crossB
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T07:26:59.800675+00:00
-- url     : https://prove2.me/theorems/dbbc21c5-a2e7-47db-a169-7363b3ab9069
-- title:
--   `BookProof.NavierStokesFlow.HermiteFarisLavine.norm_crossB` (hκ : 0 ≤ κ) (X Y : ℕ → ℂ) (n : ℕ) : ‖crossB κ X Y n‖ = amp κ n * ‖X (n + 2)‖ * ‖Y n‖
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesHermiteFarisLavine`.
--
--   `BookProof.NavierStokesFlow.HermiteFarisLavine.norm_crossB` (hκ : 0 ≤ κ) (X Y : ℕ → ℂ) (n : ℕ) : ‖crossB κ X Y n‖ = amp κ n * ‖X (n + 2)‖ * ‖Y n‖
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.HermiteFarisLavine.norm_crossB`.

-- Generated from ChapterNavierStokesHermiteFarisLavine.lean — theorem BookProof.NavierStokesFlow.HermiteFarisLavine.norm_crossB
import Mathlib
import Definitions.Def_ChapterNavierStokesHermiteFarisLavine
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.HermiteFarisLavine


open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato

variable {κ : ℝ}
variable {x : maxDom (oscSymbol κ)}

theorem BookProof.NavierStokesFlow.HermiteFarisLavine.norm_crossB (hκ : 0 ≤ κ) (X Y : ℕ → ℂ) (n : ℕ) :
    ‖crossB κ X Y n‖ = amp κ n * ‖X (n + 2)‖ * ‖Y n‖ := by sorry
