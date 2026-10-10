-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_HermiteFarisLavine_nsH_symmetricOn
-- name    : BookProof.NavierStokesFlow.HermiteFarisLavine.nsH_symmetricOn
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T07:27:41.161539+00:00
-- url     : https://prove2.me/theorems/df332166-dbf5-4dd6-994d-b7404880e164
-- title:
--   `BookProof.NavierStokesFlow.HermiteFarisLavine.nsH_symmetricOn` (hκ : 0 ≤ κ) : SymmetricOn (maxDom (oscSymbol κ)) (nsH κ hκ)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesHermiteFarisLavine`.
--
--   `BookProof.NavierStokesFlow.HermiteFarisLavine.nsH_symmetricOn` (hκ : 0 ≤ κ) : SymmetricOn (maxDom (oscSymbol κ)) (nsH κ hκ)
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.HermiteFarisLavine.nsH_symmetricOn`.

-- Generated from ChapterNavierStokesHermiteFarisLavine.lean — theorem BookProof.NavierStokesFlow.HermiteFarisLavine.nsH_symmetricOn
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

theorem BookProof.NavierStokesFlow.HermiteFarisLavine.nsH_symmetricOn (hκ : 0 ≤ κ) : SymmetricOn (maxDom (oscSymbol κ)) (nsH κ hκ) := by sorry
