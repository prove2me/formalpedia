-- Prove2me | Theorems.Thm_BookProof_QuantumGravityFock_qgGradedFock_not_bounded
-- name    : BookProof.QuantumGravityFock.qgGradedFock_not_bounded
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-16T23:38:13.418026+00:00
-- url     : https://prove2.me/theorems/36a16362-5fda-43f3-88e2-b6208f884af1
-- title:
--   `BookProof.QuantumGravityFock.qgGradedFock_not_bounded` (omega g : ℕ → ℝ) (homega : omega = 0) (hg : ∀ C : ℝ, ∃ a, C < |g a|) : ¬ ∃ C : ℝ, ∀ f : lpFiniteModes GradedIdx,...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQuantumGravityFock`.
--
--   `BookProof.QuantumGravityFock.qgGradedFock_not_bounded` (omega g : ℕ → ℝ) (homega : omega = 0) (hg : ∀ C : ℝ, ∃ a, C < |g a|) : ¬ ∃ C : ℝ, ∀ f : lpFiniteModes GradedIdx, ‖qgGradedHam omega g f‖ ≤ C * ‖f‖
--
--   Formalization note: Lean 4 identifier `BookProof.QuantumGravityFock.qgGradedFock_not_bounded`.

-- Generated from ChapterQuantumGravityFock.lean — theorem BookProof.QuantumGravityFock.qgGradedFock_not_bounded
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesFockSpace
import Definitions.Def_ChapterNavierStokesFullEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterComplexShiftCore
import Mathlib
import Definitions.Def_ChapterQuantumGravityFock
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterYangMillsGhostSector
open BookProof.FockOneParticleGap
open BookProof.FockSecondQuantization
open BookProof.YangMillsGhost
open BookProof.QuantumGravityFock



open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.NavierStokesFlow.FockOfFock BookProof.NavierStokesFlow.FullEsa
open BookProof.FarisLavine BookProof.StoneBridge BookProof.EsaClosure
open BookProof.ChapterStoneResolvent BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.HashimotoShiftInvert
open BookProof.FockSecondQuantization

noncomputable section

theorem BookProof.QuantumGravityFock.qgGradedFock_not_bounded (omega g : ℕ → ℝ) (homega : omega = 0)
    (hg : ∀ C : ℝ, ∃ a, C < |g a|) :
    ¬ ∃ C : ℝ, ∀ f : lpFiniteModes GradedIdx, ‖qgGradedHam omega g f‖ ≤ C * ‖f‖ := by sorry
