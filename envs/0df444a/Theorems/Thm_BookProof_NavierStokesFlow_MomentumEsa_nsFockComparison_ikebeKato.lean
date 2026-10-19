-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_MomentumEsa_nsFockComparison_ikebeKato
-- name    : BookProof.NavierStokesFlow.MomentumEsa.nsFockComparison_ikebeKato
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T19:22:05.37882+00:00
-- url     : https://prove2.me/theorems/45a0046b-7253-44bd-a84c-e4913451777d
-- title:
--   `BookProof.NavierStokesFlow.MomentumEsa.nsFockComparison_ikebeKato` (d : ℕ) (p q : Fin d → ℕ → ℝ) : EssentiallySelfAdjointOn (lpFiniteModes Config) ((diagMax (nsFockSymbol d p q)).
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesMomentumEsa`.
--
--   `BookProof.NavierStokesFlow.MomentumEsa.nsFockComparison_ikebeKato` (d : ℕ) (p q : Fin d → ℕ → ℝ) : EssentiallySelfAdjointOn (lpFiniteModes Config) ((diagMax (nsFockSymbol d p q)).comp (Submodule.inclusion (finiteModes_le_maxDom (nsFockSymbol d p q))))
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.MomentumEsa.nsFockComparison_ikebeKato`.

-- Generated from ChapterNavierStokesMomentumEsa.lean — theorem BookProof.NavierStokesFlow.MomentumEsa.nsFockComparison_ikebeKato
import Mathlib
import Definitions.Def_ChapterNavierStokesMomentumEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesGaugeY
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesGaugeY
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.MomentumEsa




open LpNat BookProof.FarisLavine IkebeKato FarisLavineLift DiagonalEsa

variable {ι : Type*}

theorem BookProof.NavierStokesFlow.MomentumEsa.nsFockComparison_ikebeKato (d : ℕ) (p q : Fin d → ℕ → ℝ) :
    EssentiallySelfAdjointOn (lpFiniteModes Config)
      ((diagMax (nsFockSymbol d p q)).comp
        (Submodule.inclusion (finiteModes_le_maxDom (nsFockSymbol d p q)))) := by sorry
