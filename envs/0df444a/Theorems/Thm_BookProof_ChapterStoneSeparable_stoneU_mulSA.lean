-- Prove2me | Theorems.Thm_BookProof_ChapterStoneSeparable_stoneU_mulSA
-- name    : BookProof.ChapterStoneSeparable.stoneU_mulSA
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-20T05:01:31.106918+00:00
-- url     : https://prove2.me/theorems/35fe22d7-7c14-49b9-a44f-db95d3f8e958
-- title:
--   `BookProof.ChapterStoneSeparable.stoneU_mulSA` (f : ℤ → ℝ) (t : ℝ) (psi : L2Z) : (mulSA f).stoneU t psi = phaseUnitary f (-t) psi
-- statement:
--   Prove the following Lean 4 theorem from `ChapterStoneSeparable`.
--
--   `BookProof.ChapterStoneSeparable.stoneU_mulSA` (f : ℤ → ℝ) (t : ℝ) (psi : L2Z) : (mulSA f).stoneU t psi = phaseUnitary f (-t) psi
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterStoneSeparable.stoneU_mulSA`.

-- Generated from ChapterStoneSeparable.lean — theorem BookProof.ChapterStoneSeparable.stoneU_mulSA
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterStoneConverse
import Mathlib
import Definitions.Def_ChapterStoneSeparable
import Definitions.Def_ChapterContinuityUnitaryInfinite
import Definitions.Def_ChapterStoneUnitary
import Definitions.Def_ChapterUnboundedPosition
open BookProof.ChapterContinuityUnitaryInfinite
open BookProof.ChapterUnboundedPosition
open BookProof.ChapterStoneSeparable


open scoped InnerProductSpace
open Filter Topology


open BookProof.ChapterStoneResolvent BookProof.ChapterStoneMeasurable

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

theorem BookProof.ChapterStoneSeparable.stoneU_mulSA (f : ℤ → ℝ) (t : ℝ) (psi : L2Z) :
    (mulSA f).stoneU t psi = phaseUnitary f (-t) psi := by sorry
