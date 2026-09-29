-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_LagrangianKatoRellich_hFull_hasZeroDeficiencyOn
-- name    : BookProof.NavierStokesFlow.LagrangianKatoRellich.hFull_hasZeroDeficiencyOn
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-13T00:19:42.714302+00:00
-- url     : https://prove2.me/theorems/a5302cd1-78a8-456c-b959-2634cfbc8291
-- title:
--   The Lean 4 theorem `hFull_hasZeroDeficiencyOn` in the `ChapterNavierStokesLagrangianKatoRellich` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `hFull_hasZeroDeficiencyOn` in the `ChapterNavierStokesLagrangianKatoRellich` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesLagrangianKatoRellich.lean

-- Generated from ChapterNavierStokesLagrangianKatoRellich.lean — theorem BookProof.NavierStokesFlow.LagrangianKatoRellich.hFull_hasZeroDeficiencyOn
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

theorem BookProof.NavierStokesFlow.LagrangianKatoRellich.hFull_hasZeroDeficiencyOn [CompleteSpace F] {kap kap' cc : ℝ}
    (hkap : 0 ≤ kap) (hkap' : 0 ≤ kap') (hcc : 0 ≤ cc)
    (hdrift : ∀ v : L.D,
      ‖(L.drift v : F)‖ ≤ kap * (∑ j : Fin 3, ‖(L.P j v : F)‖) + kap' * ‖(v : F)‖)
    (hC : ∀ v : L.D, ‖(L.constraintOp v : F)‖ ≤ cc * ‖(v : F)‖)
    (hT : HasZeroDeficiencyOn L.D (secondOrder L)) :
    HasZeroDeficiencyOn L.D L.hFull := by sorry
