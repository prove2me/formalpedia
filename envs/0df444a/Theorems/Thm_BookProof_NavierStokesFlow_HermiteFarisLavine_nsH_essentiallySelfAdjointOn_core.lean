-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_HermiteFarisLavine_nsH_essentiallySelfAdjointOn_core
-- name    : BookProof.NavierStokesFlow.HermiteFarisLavine.nsH_essentiallySelfAdjointOn_core
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-11T19:20:19.198131+00:00
-- url     : https://prove2.me/theorems/5f6d5a9a-0830-4ef7-a86e-1e46755610ae
-- title:
--   `BookProof.NavierStokesFlow.HermiteFarisLavine.nsH_essentiallySelfAdjointOn_core` (hκ : 0 ≤ κ) : EssentiallySelfAdjointOn (lpFiniteModes ℕ) ((nsH κ hκ).comp (Submodule.inclusion (f
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesHermiteFarisLavine`.
--
--   `BookProof.NavierStokesFlow.HermiteFarisLavine.nsH_essentiallySelfAdjointOn_core` (hκ : 0 ≤ κ) : EssentiallySelfAdjointOn (lpFiniteModes ℕ) ((nsH κ hκ).comp (Submodule.inclusion (finiteModes_le_maxDom (oscSymbol κ))))
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.HermiteFarisLavine.nsH_essentiallySelfAdjointOn_core`.

-- Generated from ChapterNavierStokesHermiteFarisLavine.lean — theorem BookProof.NavierStokesFlow.HermiteFarisLavine.nsH_essentiallySelfAdjointOn_core
import Mathlib
import Definitions.Def_ChapterNavierStokesHermiteFarisLavine
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.HermiteFarisLavine


open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato

variable {κ : ℝ}
variable {x : maxDom (oscSymbol κ)}

theorem BookProof.NavierStokesFlow.HermiteFarisLavine.nsH_essentiallySelfAdjointOn_core (hκ : 0 ≤ κ) :
    EssentiallySelfAdjointOn (lpFiniteModes ℕ)
      ((nsH κ hκ).comp (Submodule.inclusion (finiteModes_le_maxDom (oscSymbol κ)))) := by sorry
