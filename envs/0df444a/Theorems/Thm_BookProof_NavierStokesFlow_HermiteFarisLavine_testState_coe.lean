-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_HermiteFarisLavine_testState_coe
-- name    : BookProof.NavierStokesFlow.HermiteFarisLavine.testState_coe
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T07:29:01.490992+00:00
-- url     : https://prove2.me/theorems/58b6aa42-87f8-409f-a9b3-1cc2b56ded6a
-- title:
--   `BookProof.NavierStokesFlow.HermiteFarisLavine.testState_coe` (κ : ℝ) (n : ℕ) : ((testState κ : L2I ℕ) : ℕ → ℂ) n = if n = 0 then 1 else if n = 2 then 1 else 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesHermiteFarisLavine`.
--
--   `BookProof.NavierStokesFlow.HermiteFarisLavine.testState_coe` (κ : ℝ) (n : ℕ) : ((testState κ : L2I ℕ) : ℕ → ℂ) n = if n = 0 then 1 else if n = 2 then 1 else 0
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.HermiteFarisLavine.testState_coe`.

-- Generated from ChapterNavierStokesHermiteFarisLavine.lean — theorem BookProof.NavierStokesFlow.HermiteFarisLavine.testState_coe
import Mathlib
import Definitions.Def_ChapterNavierStokesHermiteFarisLavine
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

theorem BookProof.NavierStokesFlow.HermiteFarisLavine.testState_coe (κ : ℝ) (n : ℕ) :
    ((testState κ : L2I ℕ) : ℕ → ℂ) n = if n = 0 then 1 else if n = 2 then 1 else 0 := by sorry
