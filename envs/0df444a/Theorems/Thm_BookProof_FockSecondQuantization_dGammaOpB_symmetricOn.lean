-- Prove2me | Theorems.Thm_BookProof_FockSecondQuantization_dGammaOpB_symmetricOn
-- name    : BookProof.FockSecondQuantization.dGammaOpB_symmetricOn
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T13:28:47.691322+00:00
-- url     : https://prove2.me/theorems/3a653c40-6d46-41f2-8e3e-523d4e325d1f
-- title:
--   {ε : ℕ ≃ Conf} {col : ℕ → (ℕ →₀ ℂ)} (hherm : IsHermCol col) : SymmetricOn (finiteModeDomain (fockBasisN ε)) (dGammaOpB ε col)
-- statement:
--   Lean 4 theorem `BookProof.FockSecondQuantization.dGammaOpB_symmetricOn` (module `BookProof.FockSecondQuantization`), source chapter `BookProof/ChapterFockSecondQuantization.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterFockSecondQuantization.lean

-- Generated from ChapterFockSecondQuantization.lean — theorem BookProof.FockSecondQuantization.dGammaOpB_symmetricOn
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

theorem BookProof.FockSecondQuantization.dGammaOpB_symmetricOn {ε : ℕ ≃ Conf} {col : ℕ → (ℕ →₀ ℂ)} (hherm : IsHermCol col) :
    SymmetricOn (finiteModeDomain (fockBasisN ε)) (dGammaOpB ε col) := by sorry
