-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_HermiteFarisLavine_abs_le_of_hasSum
-- name    : BookProof.NavierStokesFlow.HermiteFarisLavine.abs_le_of_hasSum
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T07:28:19.23+00:00
-- url     : https://prove2.me/theorems/dd390121-0065-4c63-9bf7-6213d81b60a8
-- title:
--   `BookProof.NavierStokesFlow.HermiteFarisLavine.abs_le_of_hasSum` {f g : ℕ → ℝ} {S T : ℝ} (hf : HasSum f S) (hg : HasSum g T) (h : ∀ n, |f n| ≤ g n) : |S| ≤ T
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesHermiteFarisLavine`.
--
--   `BookProof.NavierStokesFlow.HermiteFarisLavine.abs_le_of_hasSum` {f g : ℕ → ℝ} {S T : ℝ} (hf : HasSum f S) (hg : HasSum g T) (h : ∀ n, |f n| ≤ g n) : |S| ≤ T
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.HermiteFarisLavine.abs_le_of_hasSum`.

-- Generated from ChapterNavierStokesHermiteFarisLavine.lean — theorem BookProof.NavierStokesFlow.HermiteFarisLavine.abs_le_of_hasSum
import Mathlib
import Definitions.Def_ChapterNavierStokesHermiteFarisLavine
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.HermiteFarisLavine


open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato

variable {κ : ℝ}
variable {x : maxDom (oscSymbol κ)}

theorem BookProof.NavierStokesFlow.HermiteFarisLavine.abs_le_of_hasSum {f g : ℕ → ℝ} {S T : ℝ} (hf : HasSum f S) (hg : HasSum g T)
    (h : ∀ n, |f n| ≤ g n) : |S| ≤ T := by sorry
