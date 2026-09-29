-- Prove2me | Theorems.Thm_BookProof_BddBelowFiberSumEsa_fiberSumHam_stone_flow
-- name    : BookProof.BddBelowFiberSumEsa.fiberSumHam_stone_flow
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T11:11:35.478092+00:00
-- url     : https://prove2.me/theorems/7ed75ac7-8eb9-4c42-ad28-2dc0106e002a
-- title:
--   The Lean 4 theorem `fiberSumHam_stone_flow` in the `ChapterBddBelowFiberSumEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `fiberSumHam_stone_flow` in the `ChapterBddBelowFiberSumEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterBddBelowFiberSumEsa.lean

-- Generated from ChapterBddBelowFiberSumEsa.lean — theorem BookProof.BddBelowFiberSumEsa.fiberSumHam_stone_flow
import Mathlib
import Definitions.Def_ChapterBddBelowFiberSumEsa
open BookProof.BddBelowFiberSumEsa











open MeasureTheory
open BookProof.FarisLavine BookProof.ScalaronEsa BookProof.ScalaronWallEsa

noncomputable section

variable {ι : Type*}

theorem BookProof.BddBelowFiberSumEsa.fiberSumHam_stone_flow (V : ι → ℝ → ℝ)
    (hV : ∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (V i))
    (hbdd : ∀ i, ∃ K : ℝ, ∀ x, -K ≤ V i x) :
    ∃ (T : ChapterStoneResolvent.UnboundedSelfAdjoint (fiberSpace ι))
      (U : ℝ → (fiberSpace ι →L[ℂ] fiberSpace ι)),
      EsaClosure.IsSelfAdjointExtension (fiberSumHam V hV) T.op ∧ StoneBridge.IsStoneFlow T U := by sorry
