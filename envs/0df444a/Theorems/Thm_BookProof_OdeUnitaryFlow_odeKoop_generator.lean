-- Prove2me | Theorems.Thm_BookProof_OdeUnitaryFlow_odeKoop_generator
-- name    : BookProof.OdeUnitaryFlow.odeKoop_generator
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T08:42:27.779216+00:00
-- url     : https://prove2.me/theorems/a5bc65b8-c3cd-4ec2-94ac-84c052ca808e
-- title:
--   `BookProof.OdeUnitaryFlow.odeKoop_generator` (ψ : ℝ → ℂ) (x : ℝ) (d : ℂ) (hψ : HasDerivAt ψ d x) : HasDerivAt (fun t : ℝ => odeKoop t ψ x) (-Complex.I * hamValue x d (ψ x)) 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterOdeUnitaryFlow`.
--
--   `BookProof.OdeUnitaryFlow.odeKoop_generator` (ψ : ℝ → ℂ) (x : ℝ) (d : ℂ) (hψ : HasDerivAt ψ d x) : HasDerivAt (fun t : ℝ => odeKoop t ψ x) (-Complex.I * hamValue x d (ψ x)) 0
--
--   Formalization note: Lean 4 identifier `BookProof.OdeUnitaryFlow.odeKoop_generator`.

-- Generated from ChapterOdeUnitaryFlow.lean — theorem BookProof.OdeUnitaryFlow.odeKoop_generator
import Mathlib
import Definitions.Def_ChapterOdeUnitaryFlow
open BookProof.OdeUnitaryFlow



open MeasureTheory Filter Set
open scoped Topology ENNReal

theorem BookProof.OdeUnitaryFlow.odeKoop_generator (ψ : ℝ → ℂ) (x : ℝ) (d : ℂ) (hψ : HasDerivAt ψ d x) :
    HasDerivAt (fun t : ℝ => odeKoop t ψ x) (-Complex.I * hamValue x d (ψ x)) 0 := by sorry
