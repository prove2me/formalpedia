-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_HermiteFarisLavine_commForm_ne_zero_of_pos
-- name    : BookProof.NavierStokesFlow.HermiteFarisLavine.commForm_ne_zero_of_pos
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T07:28:47.659533+00:00
-- url     : https://prove2.me/theorems/68adb696-bfff-4f4b-8f29-4e058b4e51d9
-- title:
--   `BookProof.NavierStokesFlow.HermiteFarisLavine.commForm_ne_zero_of_pos` (hκ : 0 < κ) : commForm (nsH κ (le_of_lt hκ)) (diagMax (oscSymbol κ)) (testState κ) ≠ 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesHermiteFarisLavine`.
--
--   `BookProof.NavierStokesFlow.HermiteFarisLavine.commForm_ne_zero_of_pos` (hκ : 0 < κ) : commForm (nsH κ (le_of_lt hκ)) (diagMax (oscSymbol κ)) (testState κ) ≠ 0
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.HermiteFarisLavine.commForm_ne_zero_of_pos`.

-- Generated from ChapterNavierStokesHermiteFarisLavine.lean — theorem BookProof.NavierStokesFlow.HermiteFarisLavine.commForm_ne_zero_of_pos
import Mathlib
import Definitions.Def_ChapterNavierStokesHermiteFarisLavine
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterNavierStokesFockManyMode
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow.FockManyMode
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.HermiteFarisLavine


open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato

variable {κ : ℝ}
variable {x : maxDom (oscSymbol κ)}

theorem BookProof.NavierStokesFlow.HermiteFarisLavine.commForm_ne_zero_of_pos (hκ : 0 < κ) :
    commForm (nsH κ (le_of_lt hκ)) (diagMax (oscSymbol κ)) (testState κ) ≠ 0 := by sorry
