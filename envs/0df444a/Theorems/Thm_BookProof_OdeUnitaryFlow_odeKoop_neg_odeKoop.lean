-- Prove2me | Theorems.Thm_BookProof_OdeUnitaryFlow_odeKoop_neg_odeKoop
-- name    : BookProof.OdeUnitaryFlow.odeKoop_neg_odeKoop
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T19:43:44.109323+00:00
-- url     : https://prove2.me/theorems/da2b8250-119b-4068-a18f-1803068d7dd1
-- title:
--   `BookProof.OdeUnitaryFlow.odeKoop_neg_odeKoop` (t : ℝ) (ψ : ℝ → ℂ) (x : ℝ) (hx : x ∈ flowDom (-t)) : odeKoop (-t) (odeKoop t ψ) x = ψ x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterOdeUnitaryFlow`.
--
--   `BookProof.OdeUnitaryFlow.odeKoop_neg_odeKoop` (t : ℝ) (ψ : ℝ → ℂ) (x : ℝ) (hx : x ∈ flowDom (-t)) : odeKoop (-t) (odeKoop t ψ) x = ψ x
--
--   Formalization note: Lean 4 identifier `BookProof.OdeUnitaryFlow.odeKoop_neg_odeKoop`.

-- Generated from ChapterOdeUnitaryFlow.lean — theorem BookProof.OdeUnitaryFlow.odeKoop_neg_odeKoop
import Mathlib
import Definitions.Def_ChapterOdeUnitaryFlow
open BookProof.OdeUnitaryFlow



open MeasureTheory Filter Set
open scoped Topology ENNReal

theorem BookProof.OdeUnitaryFlow.odeKoop_neg_odeKoop (t : ℝ) (ψ : ℝ → ℂ) (x : ℝ) (hx : x ∈ flowDom (-t)) :
    odeKoop (-t) (odeKoop t ψ) x = ψ x := by sorry
