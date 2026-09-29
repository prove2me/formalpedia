-- Prove2me | Theorems.Thm_BookProof_FockSecondQuantization_dGammaOpB_quadForm_nonneg
-- name    : BookProof.FockSecondQuantization.dGammaOpB_quadForm_nonneg
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T13:25:18.235144+00:00
-- url     : https://prove2.me/theorems/d6ae1b52-2b3a-4de0-ba8c-8af557b44cd3
-- title:
--   {ε : ℕ ≃ Conf} {col : ℕ → (ℕ →₀ ℂ)} (hpos : IsPosCol col) (x : finiteModeDomain (fockBasisN ε)) : 0 ≤ quadForm (dGammaOpB ε col) x
-- statement:
--   Lean 4 theorem `BookProof.FockSecondQuantization.dGammaOpB_quadForm_nonneg` (module `BookProof.FockSecondQuantization`), source chapter `BookProof/ChapterFockSecondQuantization.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterFockSecondQuantization.lean

-- Generated from ChapterFockSecondQuantization.lean — theorem BookProof.FockSecondQuantization.dGammaOpB_quadForm_nonneg
import Mathlib
import Definitions.Def_ChapterFockSecondQuantization
open BookProof.FockSecondQuantization







open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension
open BookProof.HashimotoShiftInvert

noncomputable section

















































































variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]











open Filter Topology

theorem BookProof.FockSecondQuantization.dGammaOpB_quadForm_nonneg {ε : ℕ ≃ Conf} {col : ℕ → (ℕ →₀ ℂ)} (hpos : IsPosCol col)
    (x : finiteModeDomain (fockBasisN ε)) : 0 ≤ quadForm (dGammaOpB ε col) x := by sorry
