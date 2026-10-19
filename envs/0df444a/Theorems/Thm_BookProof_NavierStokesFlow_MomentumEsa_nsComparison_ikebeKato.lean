-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_MomentumEsa_nsComparison_ikebeKato
-- name    : BookProof.NavierStokesFlow.MomentumEsa.nsComparison_ikebeKato
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T19:21:05.973495+00:00
-- url     : https://prove2.me/theorems/d23b73b6-c886-451e-8017-7e2fa6782e6f
-- title:
--   `BookProof.NavierStokesFlow.MomentumEsa.nsComparison_ikebeKato` (d : ℕ) (p q : Fin d → ℕ → ℝ) : EssentiallySelfAdjointOn (lpFiniteModes ℕ) ((lpFiniteModes ℕ).subtype.comp (diagComp
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesMomentumEsa`.
--
--   `BookProof.NavierStokesFlow.MomentumEsa.nsComparison_ikebeKato` (d : ℕ) (p q : Fin d → ℕ → ℝ) : EssentiallySelfAdjointOn (lpFiniteModes ℕ) ((lpFiniteModes ℕ).subtype.comp (diagComparisonData d p q).comparison)
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.MomentumEsa.nsComparison_ikebeKato`.

-- Generated from ChapterNavierStokesMomentumEsa.lean — theorem BookProof.NavierStokesFlow.MomentumEsa.nsComparison_ikebeKato
import Mathlib
import Definitions.Def_ChapterNavierStokesMomentumEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesFarisLavineLift
import Definitions.Def_ChapterNavierStokesGaugeY
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.JacobiDeficiency
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FarisLavineLift.ComparisonData
open BookProof.NavierStokesGaugeY
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.MomentumEsa




open LpNat BookProof.FarisLavine IkebeKato FarisLavineLift DiagonalEsa

variable {ι : Type*}

theorem BookProof.NavierStokesFlow.MomentumEsa.nsComparison_ikebeKato (d : ℕ) (p q : Fin d → ℕ → ℝ) :
    EssentiallySelfAdjointOn (lpFiniteModes ℕ)
      ((lpFiniteModes ℕ).subtype.comp (diagComparisonData d p q).comparison) := by sorry
