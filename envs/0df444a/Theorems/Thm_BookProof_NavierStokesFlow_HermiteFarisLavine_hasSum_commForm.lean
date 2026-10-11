-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_HermiteFarisLavine_hasSum_commForm
-- name    : BookProof.NavierStokesFlow.HermiteFarisLavine.hasSum_commForm
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T13:05:13.662247+00:00
-- url     : https://prove2.me/theorems/f754899d-299c-4da1-b23c-13066a7576fb
-- title:
--   `BookProof.NavierStokesFlow.HermiteFarisLavine.hasSum_commForm` (hκ : 0 ≤ κ) (x : maxDom (oscSymbol κ)) : HasSum (fun n => 8 * κ * (amp κ n * ((starRingEnd ℂ) (((x : L2I ℕ) : ℕ → ℂ
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesHermiteFarisLavine`.
--
--   `BookProof.NavierStokesFlow.HermiteFarisLavine.hasSum_commForm` (hκ : 0 ≤ κ) (x : maxDom (oscSymbol κ)) : HasSum (fun n => 8 * κ * (amp κ n * ((starRingEnd ℂ) (((x : L2I ℕ) : ℕ → ℂ) n) * ((x : L2I ℕ) : ℕ → ℂ) (n + 2)).re)) (commForm (nsH κ hκ) (diagMax (oscSymbol κ)) x)
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.HermiteFarisLavine.hasSum_commForm`.

-- Generated from ChapterNavierStokesHermiteFarisLavine.lean — theorem BookProof.NavierStokesFlow.HermiteFarisLavine.hasSum_commForm
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

theorem BookProof.NavierStokesFlow.HermiteFarisLavine.hasSum_commForm (hκ : 0 ≤ κ) (x : maxDom (oscSymbol κ)) :
    HasSum (fun n => 8 * κ * (amp κ n
        * ((starRingEnd ℂ) (((x : L2I ℕ) : ℕ → ℂ) n) * ((x : L2I ℕ) : ℕ → ℂ) (n + 2)).re))
      (commForm (nsH κ hκ) (diagMax (oscSymbol κ)) x) := by sorry
