-- Prove2me | Theorems.Thm_BookProof_QgHermiteCore_memLp_scalaronSectorPotential_mul_pgFun
-- name    : BookProof.QgHermiteCore.memLp_scalaronSectorPotential_mul_pgFun
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T12:16:58.972787+00:00
-- url     : https://prove2.me/theorems/45f68372-f87b-45b0-958b-ea7b9076d833
-- title:
--   (M alpha : ℝ) (hM : 0 < M) (V3 : Polynomial ℝ) (p : MvPolynomial (Fin 2) ℂ) : MemLp (fun x : Vd 2 => ((scalaronSectorPotential M alpha V3 x : ℝ) : ℂ) * pgFun p x) 2 (volume : Measure (Vd 2))
-- statement:
--   Lean 4 theorem `BookProof.QgHermiteCore.memLp_scalaronSectorPotential_mul_pgFun` (module `BookProof.QgHermiteCore`), source chapter `BookProof/ChapterQgHermiteCore.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterQgHermiteCore.lean

-- Generated from ChapterQgHermiteCore.lean — theorem BookProof.QgHermiteCore.memLp_scalaronSectorPotential_mul_pgFun
import Mathlib
import Definitions.Def_ChapterQgHermiteCore
open BookProof.QgHermiteCore













open MeasureTheory Polynomial Filter Topology
open BookProof.HermiteCore BookProof.Starobinsky







variable {E : Type*} [NormedAddCommGroup E]





































open BookProof.HermiteProductCore

variable {d : ℕ}

theorem BookProof.QgHermiteCore.memLp_scalaronSectorPotential_mul_pgFun (M alpha : ℝ) (hM : 0 < M) (V3 : Polynomial ℝ)
    (p : MvPolynomial (Fin 2) ℂ) :
    MemLp (fun x : Vd 2 => ((scalaronSectorPotential M alpha V3 x : ℝ) : ℂ) * pgFun p x) 2
      (volume : Measure (Vd 2)) := by sorry
