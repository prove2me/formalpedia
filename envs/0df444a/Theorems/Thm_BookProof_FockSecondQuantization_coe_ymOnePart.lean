-- Prove2me | Theorems.Thm_BookProof_FockSecondQuantization_coe_ymOnePart
-- name    : BookProof.FockSecondQuantization.coe_ymOnePart
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T07:50:37.180167+00:00
-- url     : https://prove2.me/theorems/1d95e537-2b48-4802-b869-8091f62939f9
-- title:
--   (e : ℕ ≃ (Fin 99 →₀ ℕ)) (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) (x : finiteModeDomain (coreBasis e)) : ((ymOnePart e fabc x : finiteModeDomain (coreBasis e)) : L2d 99) = ymHamiltonian (coreRepBasis e)...
-- statement:
--   Lean 4 theorem `BookProof.FockSecondQuantization.coe_ymOnePart` (module `BookProof.FockSecondQuantization`), source chapter `BookProof/ChapterFockSecondQuantization.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterFockSecondQuantization.lean

-- Generated from ChapterFockSecondQuantization.lean — theorem BookProof.FockSecondQuantization.coe_ymOnePart
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
















open BookProof.YangMillsHermite BookProof.HermiteProductCore
open Filter Topology

theorem BookProof.FockSecondQuantization.coe_ymOnePart (e : ℕ ≃ (Fin 99 →₀ ℕ)) (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ)
    (x : finiteModeDomain (coreBasis e)) :
    ((ymOnePart e fabc x : finiteModeDomain (coreBasis e)) : L2d 99)
      = ymHamiltonian (coreRepBasis e) fabc x := by sorry
