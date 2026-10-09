-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_IkebeKato_ikebeKato_momentum
-- name    : BookProof.NavierStokesFlow.IkebeKato.ikebeKato_momentum
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T04:57:38.697031+00:00
-- url     : https://prove2.me/theorems/821f2586-c78c-47b0-94d7-c477d3a71949
-- title:
--   The Lean 4 theorem `ikebeKato_momentum` in the `ChapterNavierStokesIkebeKato` chapter of the timepiece formalization
-- statement:
--   Formal statement of `BookProof.NavierStokesFlow.IkebeKato.ikebeKato_momentum` from the timepiece Lean 4 formalization.
-- source:
--   https://github.com/leonardopedro/timepiece

-- Generated from ChapterNavierStokesIkebeKato.lean — theorem BookProof.NavierStokesFlow.IkebeKato.ikebeKato_momentum
import Mathlib
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.IkebeKato


open scoped ENNReal



open LpNat BookProof.FarisLavine

variable {ι : Type*}

theorem BookProof.NavierStokesFlow.IkebeKato.ikebeKato_momentum (c : ι → ℝ) (hc : ∀ k, 0 ≤ c k) :
    EssentiallySelfAdjointOn (lpFiniteModes ι)
      ((diagMax c).comp (Submodule.inclusion (finiteModes_le_maxDom c))) := by sorry
