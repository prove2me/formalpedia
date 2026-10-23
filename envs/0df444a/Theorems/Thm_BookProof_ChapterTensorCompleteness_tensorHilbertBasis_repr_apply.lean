-- Prove2me | Theorems.Thm_BookProof_ChapterTensorCompleteness_tensorHilbertBasis_repr_apply
-- name    : BookProof.ChapterTensorCompleteness.tensorHilbertBasis_repr_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-22T09:29:09.702195+00:00
-- url     : https://prove2.me/theorems/2c424cbf-26f9-4ebc-a355-fba9b53536fa
-- title:
--   `BookProof.ChapterTensorCompleteness.tensorHilbertBasis_repr_apply` (b : HilbertBasis ι ℂ (Lp ℂ 2 μ)) (c : HilbertBasis κ ℂ (Lp ℂ 2 ν)) (F : Lp ℂ 2 (μ.prod ν)) (p : ι × κ) : (tenso
-- statement:
--   Prove the following Lean 4 theorem from `ChapterTensorCompleteness`.
--
--   `BookProof.ChapterTensorCompleteness.tensorHilbertBasis_repr_apply` (b : HilbertBasis ι ℂ (Lp ℂ 2 μ)) (c : HilbertBasis κ ℂ (Lp ℂ 2 ν)) (F : Lp ℂ 2 (μ.prod ν)) (p : ι × κ) : (tensorHilbertBasis b c).repr F p = (inner ℂ (tensorOf (b p.1) (c p.2)) F : ℂ)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterTensorCompleteness.tensorHilbertBasis_repr_apply`.

-- Generated from ChapterTensorCompleteness.lean — theorem BookProof.ChapterTensorCompleteness.tensorHilbertBasis_repr_apply
import Definitions.Def_ChapterSolovayHilbertTensor
import Mathlib
import Definitions.Def_ChapterTensorCompleteness
open BookProof.ChapterTensorCompleteness


noncomputable section

open MeasureTheory ENNReal Complex Filter Topology


open BookProof.ChapterSolovayHilbertTensor

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  {μ : Measure α} {ν : Measure β} [IsFiniteMeasure μ] [IsFiniteMeasure ν]

variable {ι κ : Type*}

theorem BookProof.ChapterTensorCompleteness.tensorHilbertBasis_repr_apply
    (b : HilbertBasis ι ℂ (Lp ℂ 2 μ)) (c : HilbertBasis κ ℂ (Lp ℂ 2 ν))
    (F : Lp ℂ 2 (μ.prod ν)) (p : ι × κ) :
    (tensorHilbertBasis b c).repr F p = (inner ℂ (tensorOf (b p.1) (c p.2)) F : ℂ) := by sorry
