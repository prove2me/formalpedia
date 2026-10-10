-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_HermiteFarisLavine_tsum_shift_le
-- name    : BookProof.NavierStokesFlow.HermiteFarisLavine.tsum_shift_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T07:28:03.471889+00:00
-- url     : https://prove2.me/theorems/b325bf2c-a1a1-43c0-a924-8d84587e9727
-- title:
--   `BookProof.NavierStokesFlow.HermiteFarisLavine.tsum_shift_le` {f : ℕ → ℝ} (hf : Summable f) (hnn : ∀ n, 0 ≤ f n) : (∑' n, f (n + 2)) ≤ ∑' n, f n
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesHermiteFarisLavine`.
--
--   `BookProof.NavierStokesFlow.HermiteFarisLavine.tsum_shift_le` {f : ℕ → ℝ} (hf : Summable f) (hnn : ∀ n, 0 ≤ f n) : (∑' n, f (n + 2)) ≤ ∑' n, f n
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.HermiteFarisLavine.tsum_shift_le`.

-- Generated from ChapterNavierStokesHermiteFarisLavine.lean — theorem BookProof.NavierStokesFlow.HermiteFarisLavine.tsum_shift_le
import Mathlib
import Definitions.Def_ChapterNavierStokesHermiteFarisLavine
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.HermiteFarisLavine


open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato

variable {κ : ℝ}
variable {x : maxDom (oscSymbol κ)}

theorem BookProof.NavierStokesFlow.HermiteFarisLavine.tsum_shift_le {f : ℕ → ℝ} (hf : Summable f) (hnn : ∀ n, 0 ≤ f n) :
    (∑' n, f (n + 2)) ≤ ∑' n, f n := by sorry
