-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_LagrangianCanonical_half_lagPSq_add_nu_lagQSq
-- name    : BookProof.NavierStokesFlow.LagrangianCanonical.half_lagPSq_add_nu_lagQSq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T14:24:42.360531+00:00
-- url     : https://prove2.me/theorems/1461de98-2974-424c-91f9-3983797d828d
-- title:
--   (hnu : 0 < nu) (i : Fin 3) : (1 / 2 : ℂ) • (lagP nu i).comp (lagP nu i) + ((nu : ℝ) : ℂ) • (lagQ nu i).comp (lagQ nu i) = ((omega nu : ℝ) : ℂ) • numOp i + ((omega nu / 2 : ℝ) : ℂ) • LinearMap.id
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.LagrangianCanonical.half_lagPSq_add_nu_lagQSq` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesLagrangianCanonical.lean — theorem BookProof.NavierStokesFlow.LagrangianCanonical.half_lagPSq_add_nu_lagQSq
import Mathlib
import Definitions.Def_ChapterNavierStokesLagrangianCanonical
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.LagrangianCanonical
















open scoped ENNReal



open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato  BookProof.NavierStokesFlow.LagrangianKatoRellich
open BookProof.NavierStokesFlow.CanonicalVector BookProof.NavierStokesFlow.ThreeComponent














variable (nu : ℝ)

theorem BookProof.NavierStokesFlow.LagrangianCanonical.half_lagPSq_add_nu_lagQSq (hnu : 0 < nu) (i : Fin 3) :
    (1 / 2 : ℂ) • (lagP nu i).comp (lagP nu i)
        + ((nu : ℝ) : ℂ) • (lagQ nu i).comp (lagQ nu i)
      = ((omega nu : ℝ) : ℂ) • numOp i + ((omega nu / 2 : ℝ) : ℂ) • LinearMap.id := by sorry
