-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_HermiteFarisLavine_nsH_coe
-- name    : BookProof.NavierStokesFlow.HermiteFarisLavine.nsH_coe
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T09:32:58.125293+00:00
-- url     : https://prove2.me/theorems/db49ca01-a393-4480-aa8c-e569d7c085f8
-- title:
--   The Lean 4 theorem `nsH_coe` in the `ChapterNavierStokesHermiteFarisLavine` chapter of the timepiece formalization
-- statement:
--   Formal statement of `BookProof.NavierStokesFlow.HermiteFarisLavine.nsH_coe` from the timepiece Lean 4 formalization.
-- source:
--   https://github.com/leonardopedro/timepiece

-- Generated from ChapterNavierStokesHermiteFarisLavine.lean — theorem BookProof.NavierStokesFlow.HermiteFarisLavine.nsH_coe
import Mathlib
import Definitions.Def_ChapterNavierStokesHermiteFarisLavine
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow.IkebeKato
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.HermiteFarisLavine

variable {κ : ℝ}
variable {x : maxDom (oscSymbol κ)}


open scoped ENNReal



open LpNat IkebeKato
open BookProof.FarisLavine

theorem BookProof.NavierStokesFlow.HermiteFarisLavine.nsH_coe (hκ : 0 ≤ κ) (x : maxDom (oscSymbol κ)) (m : ℕ) :
    ((nsH κ hκ x : L2I ℕ) : ℕ → ℂ) m = hFun κ ((x : L2I ℕ) : ℕ → ℂ) m := by sorry
