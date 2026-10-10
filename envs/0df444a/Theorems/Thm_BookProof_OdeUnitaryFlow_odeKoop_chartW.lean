-- Prove2me | Theorems.Thm_BookProof_OdeUnitaryFlow_odeKoop_chartW
-- name    : BookProof.OdeUnitaryFlow.odeKoop_chartW
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T08:42:49.644994+00:00
-- url     : https://prove2.me/theorems/c11e4f34-2ee5-41f4-b61b-7718bb934ce7
-- title:
--   `BookProof.OdeUnitaryFlow.odeKoop_chartW` (t : ℝ) (ψ : ℝ → ℂ) {x : ℝ} (hx : x ≠ 0) (h : 1 + t * x ≠ 0) : odeKoop t (chartW ψ) x = chartW (transl t ψ) x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterOdeUnitaryFlow`.
--
--   `BookProof.OdeUnitaryFlow.odeKoop_chartW` (t : ℝ) (ψ : ℝ → ℂ) {x : ℝ} (hx : x ≠ 0) (h : 1 + t * x ≠ 0) : odeKoop t (chartW ψ) x = chartW (transl t ψ) x
--
--   Formalization note: Lean 4 identifier `BookProof.OdeUnitaryFlow.odeKoop_chartW`.

-- Generated from ChapterOdeUnitaryFlow.lean — theorem BookProof.OdeUnitaryFlow.odeKoop_chartW
import Mathlib
import Definitions.Def_ChapterOdeUnitaryFlow
open BookProof.OdeUnitaryFlow



open MeasureTheory Filter Set
open scoped Topology ENNReal

theorem BookProof.OdeUnitaryFlow.odeKoop_chartW (t : ℝ) (ψ : ℝ → ℂ) {x : ℝ} (hx : x ≠ 0) (h : 1 + t * x ≠ 0) :
    odeKoop t (chartW ψ) x = chartW (transl t ψ) x := by sorry
