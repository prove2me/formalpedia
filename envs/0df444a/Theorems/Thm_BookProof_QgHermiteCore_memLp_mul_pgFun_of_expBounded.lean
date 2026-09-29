-- Prove2me | Theorems.Thm_BookProof_QgHermiteCore_memLp_mul_pgFun_of_expBounded
-- name    : BookProof.QgHermiteCore.memLp_mul_pgFun_of_expBounded
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T07:58:06.749205+00:00
-- url     : https://prove2.me/theorems/c2f5d35d-f825-4af1-bab1-0f48c8424c1e
-- title:
--   {W : Vd d → ℝ} (hW : Continuous W) (hWb : ExpBounded W) (p : MvPolynomial (Fin d) ℂ) : MemLp (fun x : Vd d => ((W x : ℝ) : ℂ) * pgFun p x) 2 (volume : Measure (Vd d))
-- statement:
--   Lean 4 theorem `BookProof.QgHermiteCore.memLp_mul_pgFun_of_expBounded` (module `BookProof.QgHermiteCore`), source chapter `BookProof/ChapterQgHermiteCore.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterQgHermiteCore.lean

-- Generated from ChapterQgHermiteCore.lean — theorem BookProof.QgHermiteCore.memLp_mul_pgFun_of_expBounded
import Mathlib
import Definitions.Def_ChapterQgHermiteCore
open BookProof.QgHermiteCore













open MeasureTheory Polynomial Filter Topology
open BookProof.HermiteCore BookProof.Starobinsky







variable {E : Type*} [NormedAddCommGroup E]





































open BookProof.HermiteProductCore

variable {d : ℕ}

theorem BookProof.QgHermiteCore.memLp_mul_pgFun_of_expBounded {W : Vd d → ℝ} (hW : Continuous W) (hWb : ExpBounded W)
    (p : MvPolynomial (Fin d) ℂ) :
    MemLp (fun x : Vd d => ((W x : ℝ) : ℂ) * pgFun p x) 2 (volume : Measure (Vd d)) := by sorry
