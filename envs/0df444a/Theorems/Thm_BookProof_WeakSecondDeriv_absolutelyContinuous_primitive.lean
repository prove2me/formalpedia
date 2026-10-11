-- Prove2me | Theorems.Thm_BookProof_WeakSecondDeriv_absolutelyContinuous_primitive
-- name    : BookProof.WeakSecondDeriv.absolutelyContinuous_primitive
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T17:11:20.497068+00:00
-- url     : https://prove2.me/theorems/77bb2815-4862-4313-ba46-0bb547bb9d05
-- title:
--   `BookProof.WeakSecondDeriv.absolutelyContinuous_primitive` {G : ℝ → ℝ} (hG : LocallyIntegrable G volume) {a b c : ℝ} (hc : c ∈ uIcc a b) : AbsolutelyContinuousOnInterval (fun x =>
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWeakSecondDerivative`.
--
--   `BookProof.WeakSecondDeriv.absolutelyContinuous_primitive` {G : ℝ → ℝ} (hG : LocallyIntegrable G volume) {a b c : ℝ} (hc : c ∈ uIcc a b) : AbsolutelyContinuousOnInterval (fun x => ∫ t in c..x, G t) a b
--
--   Formalization note: Lean 4 identifier `BookProof.WeakSecondDeriv.absolutelyContinuous_primitive`.

-- Generated from ChapterWeakSecondDerivative.lean — theorem BookProof.WeakSecondDeriv.absolutelyContinuous_primitive
import Mathlib
import Definitions.Def_ChapterWeakSecondDerivative
open BookProof.WeakSecondDeriv



open MeasureTheory Filter Topology intervalIntegral Set

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem BookProof.WeakSecondDeriv.absolutelyContinuous_primitive {G : ℝ → ℝ} (hG : LocallyIntegrable G volume)
    {a b c : ℝ} (hc : c ∈ uIcc a b) :
    AbsolutelyContinuousOnInterval (fun x => ∫ t in c..x, G t) a b := by sorry
