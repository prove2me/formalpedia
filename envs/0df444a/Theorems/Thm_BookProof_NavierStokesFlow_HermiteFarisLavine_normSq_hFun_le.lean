-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_HermiteFarisLavine_normSq_hFun_le
-- name    : BookProof.NavierStokesFlow.HermiteFarisLavine.normSq_hFun_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T07:27:47.997196+00:00
-- url     : https://prove2.me/theorems/51d4e5dc-f548-4872-9dad-fd847d67c049
-- title:
--   `BookProof.NavierStokesFlow.HermiteFarisLavine.normSq_hFun_le` (hκ : 0 ≤ κ) (X : ℕ → ℂ) (m : ℕ) : ‖hFun κ X m‖ ^ 2 ≤ 2 * shift2 (fun n => (ampSeq κ X n) ^ 2) m + 2 * (ampSeq...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesHermiteFarisLavine`.
--
--   `BookProof.NavierStokesFlow.HermiteFarisLavine.normSq_hFun_le` (hκ : 0 ≤ κ) (X : ℕ → ℂ) (m : ℕ) : ‖hFun κ X m‖ ^ 2 ≤ 2 * shift2 (fun n => (ampSeq κ X n) ^ 2) m + 2 * (ampSeq κ X (m + 2)) ^ 2
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.HermiteFarisLavine.normSq_hFun_le`.

-- Generated from ChapterNavierStokesHermiteFarisLavine.lean — theorem BookProof.NavierStokesFlow.HermiteFarisLavine.normSq_hFun_le
import Mathlib
import Definitions.Def_ChapterNavierStokesHermiteFarisLavine
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.HermiteFarisLavine


open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato

variable {κ : ℝ}
variable {x : maxDom (oscSymbol κ)}

theorem BookProof.NavierStokesFlow.HermiteFarisLavine.normSq_hFun_le (hκ : 0 ≤ κ) (X : ℕ → ℂ) (m : ℕ) :
    ‖hFun κ X m‖ ^ 2
      ≤ 2 * shift2 (fun n => (ampSeq κ X n) ^ 2) m + 2 * (ampSeq κ X (m + 2)) ^ 2 := by sorry
