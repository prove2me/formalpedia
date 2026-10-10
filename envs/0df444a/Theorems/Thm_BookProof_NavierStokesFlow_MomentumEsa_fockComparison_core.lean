-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_MomentumEsa_fockComparison_core
-- name    : BookProof.NavierStokesFlow.MomentumEsa.fockComparison_core
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T07:52:06.585976+00:00
-- url     : https://prove2.me/theorems/22114d55-d654-4686-9fe4-f72346e095fa
-- title:
--   `BookProof.NavierStokesFlow.MomentumEsa.fockComparison_core` (n : ℕ → ℝ) (x : maxDom (fockSymbol n)) (ε : ℝ) (hε : 0 < ε) : ∃ y : maxDom (fockSymbol n), (y : L2I Config) ∈ lpFinite
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesMomentumEsa`.
--
--   `BookProof.NavierStokesFlow.MomentumEsa.fockComparison_core` (n : ℕ → ℝ) (x : maxDom (fockSymbol n)) (ε : ℝ) (hε : 0 < ε) : ∃ y : maxDom (fockSymbol n), (y : L2I Config) ∈ lpFiniteModes Config ∧ ‖(y : L2I Config) - (x : L2I Config)‖ < ε ∧ ‖diagMax (fockSymbol n) y - diagMax (fockSymbol n) x‖ < ε
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.MomentumEsa.fockComparison_core`.

-- Generated from ChapterNavierStokesMomentumEsa.lean — theorem BookProof.NavierStokesFlow.MomentumEsa.fockComparison_core
import Mathlib
import Definitions.Def_ChapterNavierStokesMomentumEsa
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.MomentumEsa




open LpNat BookProof.FarisLavine IkebeKato FarisLavineLift DiagonalEsa

variable {ι : Type*}

theorem BookProof.NavierStokesFlow.MomentumEsa.fockComparison_core (n : ℕ → ℝ) (x : maxDom (fockSymbol n)) (ε : ℝ) (hε : 0 < ε) :
    ∃ y : maxDom (fockSymbol n), (y : L2I Config) ∈ lpFiniteModes Config ∧
      ‖(y : L2I Config) - (x : L2I Config)‖ < ε ∧
        ‖diagMax (fockSymbol n) y - diagMax (fockSymbol n) x‖ < ε := by sorry
