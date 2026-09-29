-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_LagrangianCanonical_comm_lagP_lagQ_of_ne
-- name    : BookProof.NavierStokesFlow.LagrangianCanonical.comm_lagP_lagQ_of_ne
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T12:42:13.133443+00:00
-- url     : https://prove2.me/theorems/92663755-451d-4697-856d-acad2bc76b05
-- title:
--   {i k : Fin 3} (h : i ≠ k) : (lagP nu i).comp (lagQ nu k) = (lagQ nu k).comp (lagP nu i)
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.LagrangianCanonical.comm_lagP_lagQ_of_ne` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesLagrangianCanonical.lean — theorem BookProof.NavierStokesFlow.LagrangianCanonical.comm_lagP_lagQ_of_ne
import Mathlib
import Definitions.Def_ChapterNavierStokesLagrangianCanonical
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.LagrangianCanonical
















open scoped ENNReal



open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato  BookProof.NavierStokesFlow.LagrangianKatoRellich
open BookProof.NavierStokesFlow.CanonicalVector BookProof.NavierStokesFlow.ThreeComponent














variable (nu : ℝ)

theorem BookProof.NavierStokesFlow.LagrangianCanonical.comm_lagP_lagQ_of_ne {i k : Fin 3} (h : i ≠ k) :
    (lagP nu i).comp (lagQ nu k) = (lagQ nu k).comp (lagP nu i) := by sorry
