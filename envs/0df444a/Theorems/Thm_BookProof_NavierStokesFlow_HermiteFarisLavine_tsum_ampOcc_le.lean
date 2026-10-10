-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_HermiteFarisLavine_tsum_ampOcc_le
-- name    : BookProof.NavierStokesFlow.HermiteFarisLavine.tsum_ampOcc_le
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T07:28:38.739577+00:00
-- url     : https://prove2.me/theorems/fc34726b-e06a-4a99-826f-30a5da2918d0
-- title:
--   `BookProof.NavierStokesFlow.HermiteFarisLavine.tsum_ampOcc_le` (hκ : 0 ≤ κ) (x : maxDom (oscSymbol κ)) : (∑' n, amp κ n * ‖((x : L2I ℕ) : ℕ → ℂ) n‖ ^ 2) ≤ (1 / 4 + κ / 2) *...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesHermiteFarisLavine`.
--
--   `BookProof.NavierStokesFlow.HermiteFarisLavine.tsum_ampOcc_le` (hκ : 0 ≤ κ) (x : maxDom (oscSymbol κ)) : (∑' n, amp κ n * ‖((x : L2I ℕ) : ℕ → ℂ) n‖ ^ 2) ≤ (1 / 4 + κ / 2) * quadForm (diagMax (oscSymbol κ)) x
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.HermiteFarisLavine.tsum_ampOcc_le`.

-- Generated from ChapterNavierStokesHermiteFarisLavine.lean — theorem BookProof.NavierStokesFlow.HermiteFarisLavine.tsum_ampOcc_le
import Mathlib
import Definitions.Def_ChapterNavierStokesHermiteFarisLavine
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.HermiteFarisLavine


open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato

variable {κ : ℝ}
variable {x : maxDom (oscSymbol κ)}

theorem BookProof.NavierStokesFlow.HermiteFarisLavine.tsum_ampOcc_le (hκ : 0 ≤ κ) (x : maxDom (oscSymbol κ)) :
    (∑' n, amp κ n * ‖((x : L2I ℕ) : ℕ → ℂ) n‖ ^ 2)
      ≤ (1 / 4 + κ / 2) * quadForm (diagMax (oscSymbol κ)) x := by sorry
