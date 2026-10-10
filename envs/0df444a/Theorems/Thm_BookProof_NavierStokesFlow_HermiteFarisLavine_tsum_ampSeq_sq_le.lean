-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_HermiteFarisLavine_tsum_ampSeq_sq_le
-- name    : BookProof.NavierStokesFlow.HermiteFarisLavine.tsum_ampSeq_sq_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T07:26:44.177981+00:00
-- url     : https://prove2.me/theorems/913ec093-d68a-414b-9127-4226f770716f
-- title:
--   `BookProof.NavierStokesFlow.HermiteFarisLavine.tsum_ampSeq_sq_le` (hκ : 0 ≤ κ) (x : maxDom (oscSymbol κ)) : (∑' n, (ampSeq κ ((x : L2I ℕ) : ℕ → ℂ) n) ^ 2) ≤ (1 / 8) * ‖(diagMax (os
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesHermiteFarisLavine`.
--
--   `BookProof.NavierStokesFlow.HermiteFarisLavine.tsum_ampSeq_sq_le` (hκ : 0 ≤ κ) (x : maxDom (oscSymbol κ)) : (∑' n, (ampSeq κ ((x : L2I ℕ) : ℕ → ℂ) n) ^ 2) ≤ (1 / 8) * ‖(diagMax (oscSymbol κ) x : L2I ℕ)‖ ^ 2 + (κ ^ 2 / 2) * ‖(x : L2I ℕ)‖ ^ 2
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.HermiteFarisLavine.tsum_ampSeq_sq_le`.

-- Generated from ChapterNavierStokesHermiteFarisLavine.lean — theorem BookProof.NavierStokesFlow.HermiteFarisLavine.tsum_ampSeq_sq_le
import Mathlib
import Definitions.Def_ChapterNavierStokesHermiteFarisLavine
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.HermiteFarisLavine


open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato

variable {κ : ℝ}
variable {x : maxDom (oscSymbol κ)}

theorem BookProof.NavierStokesFlow.HermiteFarisLavine.tsum_ampSeq_sq_le (hκ : 0 ≤ κ) (x : maxDom (oscSymbol κ)) :
    (∑' n, (ampSeq κ ((x : L2I ℕ) : ℕ → ℂ) n) ^ 2)
      ≤ (1 / 8) * ‖(diagMax (oscSymbol κ) x : L2I ℕ)‖ ^ 2 + (κ ^ 2 / 2) * ‖(x : L2I ℕ)‖ ^ 2 := by sorry
