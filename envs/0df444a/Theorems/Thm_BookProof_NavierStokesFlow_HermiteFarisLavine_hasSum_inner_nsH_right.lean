-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_HermiteFarisLavine_hasSum_inner_nsH_right
-- name    : BookProof.NavierStokesFlow.HermiteFarisLavine.hasSum_inner_nsH_right
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T13:04:56.759051+00:00
-- url     : https://prove2.me/theorems/a76b4453-f3d5-43cd-ac60-fd71ee5f5ef0
-- title:
--   `BookProof.NavierStokesFlow.HermiteFarisLavine.hasSum_inner_nsH_right` (hκ : 0 ≤ κ) (x y : maxDom (oscSymbol κ)) : HasSum (fun n => -Complex.I * crossA κ ((x : L2I ℕ) : ℕ → ℂ) (((y
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesHermiteFarisLavine`.
--
--   `BookProof.NavierStokesFlow.HermiteFarisLavine.hasSum_inner_nsH_right` (hκ : 0 ≤ κ) (x y : maxDom (oscSymbol κ)) : HasSum (fun n => -Complex.I * crossA κ ((x : L2I ℕ) : ℕ → ℂ) (((y : L2I ℕ) : ℕ → ℂ)) n + Complex.I * crossB κ ((x : L2I ℕ) : ℕ → ℂ) (((y : L2I ℕ) : ℕ → ℂ)) n) (inner ℂ (x : L2I ℕ) (nsH κ hκ y : L2I ℕ))
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.HermiteFarisLavine.hasSum_inner_nsH_right`.

-- Generated from ChapterNavierStokesHermiteFarisLavine.lean — theorem BookProof.NavierStokesFlow.HermiteFarisLavine.hasSum_inner_nsH_right
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

theorem BookProof.NavierStokesFlow.HermiteFarisLavine.hasSum_inner_nsH_right (hκ : 0 ≤ κ) (x y : maxDom (oscSymbol κ)) :
    HasSum (fun n => -Complex.I * crossA κ ((x : L2I ℕ) : ℕ → ℂ) (((y : L2I ℕ) : ℕ → ℂ)) n
        + Complex.I * crossB κ ((x : L2I ℕ) : ℕ → ℂ) (((y : L2I ℕ) : ℕ → ℂ)) n)
      (inner ℂ (x : L2I ℕ) (nsH κ hκ y : L2I ℕ)) := by sorry
