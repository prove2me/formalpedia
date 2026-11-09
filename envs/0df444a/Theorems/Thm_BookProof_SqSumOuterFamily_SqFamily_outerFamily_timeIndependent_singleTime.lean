-- Prove2me | Theorems.Thm_BookProof_SqSumOuterFamily_SqFamily_outerFamily_timeIndependent_singleTime
-- name    : BookProof.SqSumOuterFamily.SqFamily.outerFamily_timeIndependent_singleTime
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-08T21:12:02.893908+00:00
-- url     : https://prove2.me/theorems/426f5fb4-fc46-4896-8507-041ea7ee22bd
-- title:
--   `BookProof.SqSumOuterFamily.SqFamily.outerFamily_timeIndependent_singleTime` (F : SqFamily) : ∃ (T : UnboundedSelfAdjoint (outerFock F.dim)) (S : ℕ → UnboundedSelfAdjoint (outerFoc
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSqSumOuterSingleTime`.
--
--   `BookProof.SqSumOuterFamily.SqFamily.outerFamily_timeIndependent_singleTime` (F : SqFamily) : ∃ (T : UnboundedSelfAdjoint (outerFock F.dim)) (S : ℕ → UnboundedSelfAdjoint (outerFock F.dim)), IsSelfAdjointExtension F.outerHam T.op ∧ (∀ N, IsSelfAdjointExtension (truncHam F N) (S N).op) ∧ (∀ t s : ℝ, prop T t s = T.stoneU (t - s)) ∧ (∀ (t s : ℝ) (x : outerFock F.dim), ‖prop T t s x‖ = ‖x‖) ∧ (∀ (t s r : ℝ) (x : outerFock F.dim), prop T t s (prop T s r x) = prop T t r x) ∧ (∀ t s h : ℝ, prop T (t + h) (s + h) = prop T t s) ∧ (∀ y : ℝ → outerFock F.dim, IsSchrodingerSolution T y → ∀ t s : ℝ, y t = prop T t s (y s)) ∧ (∀ l : ℝ, l ≠ 0 → IsShiftInvertC T.op (((l : ℝ) : ℂ) * Complex.I) (-(T.resCLM l)) ∧ (∀ N, IsShiftInvertC (S N).op (((l : ℝ) : ℂ) * Complex.I) (-((S N).resCLM l))) ∧ ∀ u : outerFock F.dim, Tendsto (fun N => -((S N).resCLM l u)) atTop (𝓝 (-(T.resCLM l u)))) ∧ ∀ (v : outerFock F.dim) (t : ℝ), Tendsto (fun N => (S N).stoneU t v) atTop (𝓝 (T.stoneU t v))
--
--   Formalization note: Lean 4 identifier `BookProof.SqSumOuterFamily.SqFamily.outerFamily_timeIndependent_singleTime`.

-- Generated from ChapterSqSumOuterSingleTime.lean — theorem BookProof.SqSumOuterFamily.SqFamily.outerFamily_timeIndependent_singleTime
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterComplexShiftCore
import Definitions.Def_ChapterSirkSingleTimeShift
import Definitions.Def_ChapterQgTimeIndependentFlowPromoted
import Definitions.Def_ChapterQgTruncationResolvent
import Definitions.Def_ChapterDirectSumEsa
import Mathlib
import Definitions.Def_ChapterSqSumOuterSingleTime
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterHashimotoComplexShifts
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterStoneResolvent
import Definitions.Def_ChapterStoneUnitary
import Definitions.Def_ChapterSqSumOuterFamily
import Definitions.Def_ChapterQgTimeIndependentFlowPromoted
import Definitions.Def_ChapterShiftedQuadraticEsa
open BookProof.EsaClosure
open BookProof.HashimotoShiftInvert
open BookProof.HermiteProductCore
open BookProof.ChapterSirkTrotterKato
open BookProof.ChapterStoneResolvent
open BookProof.ChapterStoneResolvent
open BookProof.StoneBridge



open Filter Topology
open BookProof.FarisLavine BookProof.EsaClosure BookProof.StoneBridge
open BookProof.ChapterStoneResolvent BookProof.ChapterSirkTrotterKato
open BookProof.HashimotoShiftInvert BookProof.SirkSingleTime
open BookProof.QgTimeIndependent BookProof.QgTruncationResolvent
open BookProof.DirectSumEsa BookProof.HermiteProductCore

noncomputable section

theorem BookProof.SqSumOuterFamily.SqFamily.outerFamily_timeIndependent_singleTime (F : SqFamily) :
    ∃ (T : UnboundedSelfAdjoint (outerFock F.dim))
      (S : ℕ → UnboundedSelfAdjoint (outerFock F.dim)),
      IsSelfAdjointExtension F.outerHam T.op ∧
        (∀ N, IsSelfAdjointExtension (truncHam F N) (S N).op) ∧
        (∀ t s : ℝ, prop T t s = T.stoneU (t - s)) ∧
        (∀ (t s : ℝ) (x : outerFock F.dim), ‖prop T t s x‖ = ‖x‖) ∧
        (∀ (t s r : ℝ) (x : outerFock F.dim), prop T t s (prop T s r x) = prop T t r x) ∧
        (∀ t s h : ℝ, prop T (t + h) (s + h) = prop T t s) ∧
        (∀ y : ℝ → outerFock F.dim, IsSchrodingerSolution T y →
          ∀ t s : ℝ, y t = prop T t s (y s)) ∧
        (∀ l : ℝ, l ≠ 0 →
          IsShiftInvertC T.op (((l : ℝ) : ℂ) * Complex.I) (-(T.resCLM l)) ∧
            (∀ N, IsShiftInvertC (S N).op (((l : ℝ) : ℂ) * Complex.I) (-((S N).resCLM l))) ∧
            ∀ u : outerFock F.dim,
              Tendsto (fun N => -((S N).resCLM l u)) atTop (𝓝 (-(T.resCLM l u)))) ∧
        ∀ (v : outerFock F.dim) (t : ℝ),
          Tendsto (fun N => (S N).stoneU t v) atTop (𝓝 (T.stoneU t v)) := by sorry
