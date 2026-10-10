-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_HermiteFarisLavine_nsH_commForm_bound
-- name    : BookProof.NavierStokesFlow.HermiteFarisLavine.nsH_commForm_bound
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T07:28:34.72197+00:00
-- url     : https://prove2.me/theorems/e6488d7f-4d02-4a42-9777-ab03e7ee40a6
-- title:
--   `BookProof.NavierStokesFlow.HermiteFarisLavine.nsH_commForm_bound` (hκ : 0 ≤ κ) (x : maxDom (oscSymbol κ)) : |commForm (nsH κ hκ) (diagMax (oscSymbol κ)) x| ≤ (2 * κ + 4 * κ ^ 2) *
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesHermiteFarisLavine`.
--
--   `BookProof.NavierStokesFlow.HermiteFarisLavine.nsH_commForm_bound` (hκ : 0 ≤ κ) (x : maxDom (oscSymbol κ)) : |commForm (nsH κ hκ) (diagMax (oscSymbol κ)) x| ≤ (2 * κ + 4 * κ ^ 2) * quadForm (diagMax (oscSymbol κ)) x
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.HermiteFarisLavine.nsH_commForm_bound`.

-- Generated from ChapterNavierStokesHermiteFarisLavine.lean — theorem BookProof.NavierStokesFlow.HermiteFarisLavine.nsH_commForm_bound
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

theorem BookProof.NavierStokesFlow.HermiteFarisLavine.nsH_commForm_bound (hκ : 0 ≤ κ) (x : maxDom (oscSymbol κ)) :
    |commForm (nsH κ hκ) (diagMax (oscSymbol κ)) x|
      ≤ (2 * κ + 4 * κ ^ 2) * quadForm (diagMax (oscSymbol κ)) x := by sorry
