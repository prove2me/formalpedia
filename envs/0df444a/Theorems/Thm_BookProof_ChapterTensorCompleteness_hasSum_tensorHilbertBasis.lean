-- Prove2me | Theorems.Thm_BookProof_ChapterTensorCompleteness_hasSum_tensorHilbertBasis
-- name    : BookProof.ChapterTensorCompleteness.hasSum_tensorHilbertBasis
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-22T09:29:21.711431+00:00
-- url     : https://prove2.me/theorems/089a0596-af07-4129-ae24-a25de8e570fe
-- title:
--   `BookProof.ChapterTensorCompleteness.hasSum_tensorHilbertBasis` (b : HilbertBasis ι ℂ (Lp ℂ 2 μ)) (c : HilbertBasis κ ℂ (Lp ℂ 2 ν)) (F : Lp ℂ 2 (μ.prod ν)) : HasSum (fun p : ι × κ
-- statement:
--   Prove the following Lean 4 theorem from `ChapterTensorCompleteness`.
--
--   `BookProof.ChapterTensorCompleteness.hasSum_tensorHilbertBasis` (b : HilbertBasis ι ℂ (Lp ℂ 2 μ)) (c : HilbertBasis κ ℂ (Lp ℂ 2 ν)) (F : Lp ℂ 2 (μ.prod ν)) : HasSum (fun p : ι × κ => (inner ℂ (tensorOf (b p.1) (c p.2)) F : ℂ) • tensorOf (b p.1) (c p.2)) F
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterTensorCompleteness.hasSum_tensorHilbertBasis`.

-- Generated from ChapterTensorCompleteness.lean — theorem BookProof.ChapterTensorCompleteness.hasSum_tensorHilbertBasis
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

theorem BookProof.ChapterTensorCompleteness.hasSum_tensorHilbertBasis
    (b : HilbertBasis ι ℂ (Lp ℂ 2 μ)) (c : HilbertBasis κ ℂ (Lp ℂ 2 ν))
    (F : Lp ℂ 2 (μ.prod ν)) :
    HasSum (fun p : ι × κ =>
        (inner ℂ (tensorOf (b p.1) (c p.2)) F : ℂ) • tensorOf (b p.1) (c p.2)) F := by sorry
