-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_HermiteFarisLavine_nsH_relative_bound
-- name    : BookProof.NavierStokesFlow.HermiteFarisLavine.nsH_relative_bound
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T19:19:59.158104+00:00
-- url     : https://prove2.me/theorems/b2c0055d-3685-48f7-8910-dbcd0b4c6036
-- title:
--   `BookProof.NavierStokesFlow.HermiteFarisLavine.nsH_relative_bound` (hκ : 0 ≤ κ) (x : maxDom (oscSymbol κ)) : ‖(nsH κ hκ x : L2I ℕ)‖ ^ 2 ≤ (1 / 2) * ‖(diagMax (oscSymbol κ) x : L2I
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesHermiteFarisLavine`.
--
--   `BookProof.NavierStokesFlow.HermiteFarisLavine.nsH_relative_bound` (hκ : 0 ≤ κ) (x : maxDom (oscSymbol κ)) : ‖(nsH κ hκ x : L2I ℕ)‖ ^ 2 ≤ (1 / 2) * ‖(diagMax (oscSymbol κ) x : L2I ℕ)‖ ^ 2 + (2 * κ ^ 2) * ‖(x : L2I ℕ)‖ ^ 2
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.HermiteFarisLavine.nsH_relative_bound`.

-- Generated from ChapterNavierStokesHermiteFarisLavine.lean — theorem BookProof.NavierStokesFlow.HermiteFarisLavine.nsH_relative_bound
import Mathlib
import Definitions.Def_ChapterNavierStokesHermiteFarisLavine
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesSignedShift
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.SignedShift
open BookProof.NavierStokesFlow.SignedShift.SignedHop
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.HermiteFarisLavine


open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato

variable {κ : ℝ}
variable {x : maxDom (oscSymbol κ)}

theorem BookProof.NavierStokesFlow.HermiteFarisLavine.nsH_relative_bound (hκ : 0 ≤ κ) (x : maxDom (oscSymbol κ)) :
    ‖(nsH κ hκ x : L2I ℕ)‖ ^ 2
      ≤ (1 / 2) * ‖(diagMax (oscSymbol κ) x : L2I ℕ)‖ ^ 2 + (2 * κ ^ 2) * ‖(x : L2I ℕ)‖ ^ 2 := by sorry
