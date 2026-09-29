-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_LagrangianKatoRellich_jacobiLag_drift_not_relativelyBounded
-- name    : BookProof.NavierStokesFlow.LagrangianKatoRellich.jacobiLag_drift_not_relativelyBounded
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-13T00:20:26.549416+00:00
-- url     : https://prove2.me/theorems/55146f94-b79f-4f16-8d37-24bd6f67b450
-- title:
--   The Lean 4 theorem `jacobiLag_drift_not_relativelyBounded` in the `ChapterNavierStokesLagrangianKatoRellich` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `jacobiLag_drift_not_relativelyBounded` in the `ChapterNavierStokesLagrangianKatoRellich` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesLagrangianKatoRellich.lean

-- Generated from ChapterNavierStokesLagrangianKatoRellich.lean — theorem BookProof.NavierStokesFlow.LagrangianKatoRellich.jacobiLag_drift_not_relativelyBounded
import Mathlib
import Definitions.Def_ChapterNavierStokesLagrangianKatoRellich
import Definitions.Def_ChapterSirkBandLedger
import Definitions.Def_ChapterRitzCertificate
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.LagrangianKatoRellich
open Filter Topology
open BookProof.NavierStokesFlow.FullEsa BookProof.NavierStokesFlow.LagrangianEsa BookProof.FarisLavine
open BookProof.EsaClosure BookProof.HashimotoShiftInvert BookProof.HermiteGalerkin
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable (L : LagrangianFullData F)


























variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable (L : LagrangianFullData F)








open BookProof.NavierStokesFlow.LpNat BookProof.NavierStokesFlow.DiagonalEsa
open BookProof.NavierStokesFlow.LpNat BookProof.NavierStokesFlow.JacobiDeficiency
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem BookProof.NavierStokesFlow.LagrangianKatoRellich.jacobiLag_drift_not_relativelyBounded :
    ¬ ∃ kap kap' : ℝ, 0 ≤ kap ∧ 0 ≤ kap' ∧ ∀ v : jacobiLagData.D,
      ‖(jacobiLagData.drift v : L2N)‖
        ≤ kap * (∑ j : Fin 3, ‖(jacobiLagData.P j v : L2N)‖) + kap' * ‖(v : L2N)‖ := by sorry
