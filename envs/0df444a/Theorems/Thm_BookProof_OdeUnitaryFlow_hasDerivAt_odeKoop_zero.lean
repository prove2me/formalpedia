-- Prove2me | Theorems.Thm_BookProof_OdeUnitaryFlow_hasDerivAt_odeKoop_zero
-- name    : BookProof.OdeUnitaryFlow.hasDerivAt_odeKoop_zero
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T13:05:18.148863+00:00
-- url     : https://prove2.me/theorems/60bf6de6-14ff-4259-8fdb-9c338317e485
-- title:
--   `BookProof.OdeUnitaryFlow.hasDerivAt_odeKoop_zero` (ψ : ℝ → ℂ) (x : ℝ) (d : ℂ) (hψ : HasDerivAt ψ d x) : HasDerivAt (fun t : ℝ => odeKoop t ψ x) (-((x : ℂ) ^ 2 * d + (x : ℂ)...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterOdeUnitaryFlow`.
--
--   `BookProof.OdeUnitaryFlow.hasDerivAt_odeKoop_zero` (ψ : ℝ → ℂ) (x : ℝ) (d : ℂ) (hψ : HasDerivAt ψ d x) : HasDerivAt (fun t : ℝ => odeKoop t ψ x) (-((x : ℂ) ^ 2 * d + (x : ℂ) * ψ x)) 0
--
--   Formalization note: Lean 4 identifier `BookProof.OdeUnitaryFlow.hasDerivAt_odeKoop_zero`.

-- Generated from ChapterOdeUnitaryFlow.lean — theorem BookProof.OdeUnitaryFlow.hasDerivAt_odeKoop_zero
import Mathlib
import Definitions.Def_ChapterOdeUnitaryFlow
open BookProof.OdeUnitaryFlow



open MeasureTheory Filter Set
open scoped Topology ENNReal

theorem BookProof.OdeUnitaryFlow.hasDerivAt_odeKoop_zero (ψ : ℝ → ℂ) (x : ℝ) (d : ℂ) (hψ : HasDerivAt ψ d x) :
    HasDerivAt (fun t : ℝ => odeKoop t ψ x) (-((x : ℂ) ^ 2 * d + (x : ℂ) * ψ x)) 0 := by sorry
