-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_HermiteFarisLavine_hasSum_inner_nsH_left
-- name    : BookProof.NavierStokesFlow.HermiteFarisLavine.hasSum_inner_nsH_left
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T13:04:41.919695+00:00
-- url     : https://prove2.me/theorems/b4769f84-3bb3-4b0d-8518-dc772d94718c
-- title:
--   `BookProof.NavierStokesFlow.HermiteFarisLavine.hasSum_inner_nsH_left` (hκ : 0 ≤ κ) (x : maxDom (oscSymbol κ)) (y : L2I ℕ) : HasSum (fun n => -Complex.I * crossA κ ((x : L2I ℕ) : ℕ
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesHermiteFarisLavine`.
--
--   `BookProof.NavierStokesFlow.HermiteFarisLavine.hasSum_inner_nsH_left` (hκ : 0 ≤ κ) (x : maxDom (oscSymbol κ)) (y : L2I ℕ) : HasSum (fun n => -Complex.I * crossA κ ((x : L2I ℕ) : ℕ → ℂ) ((y : ℕ → ℂ)) n + Complex.I * crossB κ ((x : L2I ℕ) : ℕ → ℂ) ((y : ℕ → ℂ)) n) (inner ℂ (nsH κ hκ x : L2I ℕ) y)
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.HermiteFarisLavine.hasSum_inner_nsH_left`.

-- Generated from ChapterNavierStokesHermiteFarisLavine.lean — theorem BookProof.NavierStokesFlow.HermiteFarisLavine.hasSum_inner_nsH_left
import Mathlib
import Definitions.Def_ChapterNavierStokesHermiteFarisLavine
import Definitions.Def_ChapterContinuityUnitaryInfinite
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.ChapterContinuityUnitaryInfinite
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.HermiteFarisLavine


open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato

variable {κ : ℝ}
variable {x : maxDom (oscSymbol κ)}

theorem BookProof.NavierStokesFlow.HermiteFarisLavine.hasSum_inner_nsH_left (hκ : 0 ≤ κ) (x : maxDom (oscSymbol κ)) (y : L2I ℕ) :
    HasSum (fun n => -Complex.I * crossA κ ((x : L2I ℕ) : ℕ → ℂ) ((y : ℕ → ℂ)) n
        + Complex.I * crossB κ ((x : L2I ℕ) : ℕ → ℂ) ((y : ℕ → ℂ)) n)
      (inner ℂ (nsH κ hκ x : L2I ℕ) y) := by sorry
