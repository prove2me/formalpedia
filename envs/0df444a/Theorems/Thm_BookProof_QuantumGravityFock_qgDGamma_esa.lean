-- Prove2me | Theorems.Thm_BookProof_QuantumGravityFock_qgDGamma_esa
-- name    : BookProof.QuantumGravityFock.qgDGamma_esa
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-16T23:46:27.039992+00:00
-- url     : https://prove2.me/theorems/d22c1f05-f3d0-43ef-8eab-7003e5f3354d
-- title:
--   `BookProof.QuantumGravityFock.qgDGamma_esa` (omega : ℕ → ℝ) : HasZeroDeficiencyOn (BookProof.NavierStokesFlow.FockOfFock.FockDom ℕ) (BookProof.NavierStokesFlow.FockOfFock.dGamma om
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQuantumGravityFock`.
--
--   `BookProof.QuantumGravityFock.qgDGamma_esa` (omega : ℕ → ℝ) : HasZeroDeficiencyOn (BookProof.NavierStokesFlow.FockOfFock.FockDom ℕ) (BookProof.NavierStokesFlow.FockOfFock.dGamma omega)
--
--   Formalization note: Lean 4 identifier `BookProof.QuantumGravityFock.qgDGamma_esa`.

-- Generated from ChapterQuantumGravityFock.lean — theorem BookProof.QuantumGravityFock.qgDGamma_esa
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
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
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterNavierStokesFlow
import Definitions.Def_ChapterNavierStokesFockSpace
open BookProof.FockSecondQuantization
open BookProof.NavierStokesFlow.FockOfFock
open BookProof.QuantumGravityFock



open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.NavierStokesFlow.FockOfFock BookProof.NavierStokesFlow.FullEsa
open BookProof.FarisLavine BookProof.StoneBridge BookProof.EsaClosure
open BookProof.ChapterStoneResolvent BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.HashimotoShiftInvert
open BookProof.FockSecondQuantization

noncomputable section

theorem BookProof.QuantumGravityFock.qgDGamma_esa (omega : ℕ → ℝ) :
    HasZeroDeficiencyOn (BookProof.NavierStokesFlow.FockOfFock.FockDom ℕ)
      (BookProof.NavierStokesFlow.FockOfFock.dGamma omega) := by sorry
