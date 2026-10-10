-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_HermiteFarisLavine_summable_crossA
-- name    : BookProof.NavierStokesFlow.HermiteFarisLavine.summable_crossA
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T07:27:57.522216+00:00
-- url     : https://prove2.me/theorems/981a79f8-54d8-4279-8592-1a5081eb2a4d
-- title:
--   `BookProof.NavierStokesFlow.HermiteFarisLavine.summable_crossA` (hκ : 0 ≤ κ) {X Y : ℕ → ℂ} (hX : Summable fun n => (ampSeq κ X n) ^ 2) (hY : Summable fun n => ‖Y n‖ ^ 2) : Summable
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesHermiteFarisLavine`.
--
--   `BookProof.NavierStokesFlow.HermiteFarisLavine.summable_crossA` (hκ : 0 ≤ κ) {X Y : ℕ → ℂ} (hX : Summable fun n => (ampSeq κ X n) ^ 2) (hY : Summable fun n => ‖Y n‖ ^ 2) : Summable (crossA κ X Y)
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.HermiteFarisLavine.summable_crossA`.

-- Generated from ChapterNavierStokesHermiteFarisLavine.lean — theorem BookProof.NavierStokesFlow.HermiteFarisLavine.summable_crossA
import Mathlib
import Definitions.Def_ChapterNavierStokesHermiteFarisLavine
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.HermiteFarisLavine


open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato

variable {κ : ℝ}
variable {x : maxDom (oscSymbol κ)}

theorem BookProof.NavierStokesFlow.HermiteFarisLavine.summable_crossA (hκ : 0 ≤ κ) {X Y : ℕ → ℂ}
    (hX : Summable fun n => (ampSeq κ X n) ^ 2) (hY : Summable fun n => ‖Y n‖ ^ 2) :
    Summable (crossA κ X Y) := by sorry
