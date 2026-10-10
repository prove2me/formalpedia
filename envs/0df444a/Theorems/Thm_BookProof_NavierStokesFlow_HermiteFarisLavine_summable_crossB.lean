-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_HermiteFarisLavine_summable_crossB
-- name    : BookProof.NavierStokesFlow.HermiteFarisLavine.summable_crossB
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T07:27:18.373609+00:00
-- url     : https://prove2.me/theorems/2bd7c0e0-5ae0-4c37-9af6-5b3f01995883
-- title:
--   `BookProof.NavierStokesFlow.HermiteFarisLavine.summable_crossB` (hκ : 0 ≤ κ) {X Y : ℕ → ℂ} (hX : Summable fun n => (ampSeq κ X n) ^ 2) (hY : Summable fun n => ‖Y n‖ ^ 2) : Summable
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesHermiteFarisLavine`.
--
--   `BookProof.NavierStokesFlow.HermiteFarisLavine.summable_crossB` (hκ : 0 ≤ κ) {X Y : ℕ → ℂ} (hX : Summable fun n => (ampSeq κ X n) ^ 2) (hY : Summable fun n => ‖Y n‖ ^ 2) : Summable (crossB κ X Y)
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.HermiteFarisLavine.summable_crossB`.

-- Generated from ChapterNavierStokesHermiteFarisLavine.lean — theorem BookProof.NavierStokesFlow.HermiteFarisLavine.summable_crossB
import Mathlib
import Definitions.Def_ChapterNavierStokesHermiteFarisLavine
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.HermiteFarisLavine


open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato

variable {κ : ℝ}
variable {x : maxDom (oscSymbol κ)}

theorem BookProof.NavierStokesFlow.HermiteFarisLavine.summable_crossB (hκ : 0 ≤ κ) {X Y : ℕ → ℂ}
    (hX : Summable fun n => (ampSeq κ X n) ^ 2) (hY : Summable fun n => ‖Y n‖ ^ 2) :
    Summable (crossB κ X Y) := by sorry
