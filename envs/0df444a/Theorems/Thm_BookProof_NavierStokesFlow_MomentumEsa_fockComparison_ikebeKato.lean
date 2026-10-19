-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_MomentumEsa_fockComparison_ikebeKato
-- name    : BookProof.NavierStokesFlow.MomentumEsa.fockComparison_ikebeKato
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T19:21:27.084808+00:00
-- url     : https://prove2.me/theorems/54e7da5e-ba6c-40f4-87a0-75fd32bdef47
-- title:
--   `BookProof.NavierStokesFlow.MomentumEsa.fockComparison_ikebeKato` (n : ℕ → ℝ) (hn : ∀ k, 0 ≤ n k) : EssentiallySelfAdjointOn (lpFiniteModes Config) ((diagMax (fockSymbol n)).comp (
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesMomentumEsa`.
--
--   `BookProof.NavierStokesFlow.MomentumEsa.fockComparison_ikebeKato` (n : ℕ → ℝ) (hn : ∀ k, 0 ≤ n k) : EssentiallySelfAdjointOn (lpFiniteModes Config) ((diagMax (fockSymbol n)).comp (Submodule.inclusion (finiteModes_le_maxDom (fockSymbol n))))
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.MomentumEsa.fockComparison_ikebeKato`.

-- Generated from ChapterNavierStokesMomentumEsa.lean — theorem BookProof.NavierStokesFlow.MomentumEsa.fockComparison_ikebeKato
import Mathlib
import Definitions.Def_ChapterNavierStokesMomentumEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.MomentumEsa




open LpNat BookProof.FarisLavine IkebeKato FarisLavineLift DiagonalEsa

variable {ι : Type*}

theorem BookProof.NavierStokesFlow.MomentumEsa.fockComparison_ikebeKato (n : ℕ → ℝ) (hn : ∀ k, 0 ≤ n k) :
    EssentiallySelfAdjointOn (lpFiniteModes Config)
      ((diagMax (fockSymbol n)).comp
        (Submodule.inclusion (finiteModes_le_maxDom (fockSymbol n)))) := by sorry
