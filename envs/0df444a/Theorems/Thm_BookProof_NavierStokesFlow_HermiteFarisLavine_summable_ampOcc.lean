-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_HermiteFarisLavine_summable_ampOcc
-- name    : BookProof.NavierStokesFlow.HermiteFarisLavine.summable_ampOcc
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T07:29:29.79581+00:00
-- url     : https://prove2.me/theorems/590b2b35-a961-49c1-990b-66e4d13f474f
-- title:
--   `BookProof.NavierStokesFlow.HermiteFarisLavine.summable_ampOcc` (hκ : 0 ≤ κ) (x : maxDom (oscSymbol κ)) : Summable (fun n => amp κ n * ‖((x : L2I ℕ) : ℕ → ℂ) n‖ ^ 2)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesHermiteFarisLavine`.
--
--   `BookProof.NavierStokesFlow.HermiteFarisLavine.summable_ampOcc` (hκ : 0 ≤ κ) (x : maxDom (oscSymbol κ)) : Summable (fun n => amp κ n * ‖((x : L2I ℕ) : ℕ → ℂ) n‖ ^ 2)
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.HermiteFarisLavine.summable_ampOcc`.

-- Generated from ChapterNavierStokesHermiteFarisLavine.lean — theorem BookProof.NavierStokesFlow.HermiteFarisLavine.summable_ampOcc
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

theorem BookProof.NavierStokesFlow.HermiteFarisLavine.summable_ampOcc (hκ : 0 ≤ κ) (x : maxDom (oscSymbol κ)) :
    Summable (fun n => amp κ n * ‖((x : L2I ℕ) : ℕ → ℂ) n‖ ^ 2) := by sorry
