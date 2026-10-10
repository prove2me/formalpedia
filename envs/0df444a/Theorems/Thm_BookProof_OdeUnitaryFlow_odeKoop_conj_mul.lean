-- Prove2me | Theorems.Thm_BookProof_OdeUnitaryFlow_odeKoop_conj_mul
-- name    : BookProof.OdeUnitaryFlow.odeKoop_conj_mul
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T08:43:03.488973+00:00
-- url     : https://prove2.me/theorems/587ccbe3-a365-44cd-a59f-337639e512b8
-- title:
--   `BookProof.OdeUnitaryFlow.odeKoop_conj_mul` (t : ℝ) (ρ ψ : ℝ → ℂ) (x : ℝ) (hx : x ∈ flowDom t) : odeKoop t (fun y => ρ y * odeKoop (-t) ψ y) x = ρ (mob t x) * ψ x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterOdeUnitaryFlow`.
--
--   `BookProof.OdeUnitaryFlow.odeKoop_conj_mul` (t : ℝ) (ρ ψ : ℝ → ℂ) (x : ℝ) (hx : x ∈ flowDom t) : odeKoop t (fun y => ρ y * odeKoop (-t) ψ y) x = ρ (mob t x) * ψ x
--
--   Formalization note: Lean 4 identifier `BookProof.OdeUnitaryFlow.odeKoop_conj_mul`.

-- Generated from ChapterOdeUnitaryFlow.lean — theorem BookProof.OdeUnitaryFlow.odeKoop_conj_mul
import Mathlib
import Definitions.Def_ChapterOdeUnitaryFlow
open BookProof.OdeUnitaryFlow



open MeasureTheory Filter Set
open scoped Topology ENNReal

theorem BookProof.OdeUnitaryFlow.odeKoop_conj_mul (t : ℝ) (ρ ψ : ℝ → ℂ) (x : ℝ) (hx : x ∈ flowDom t) :
    odeKoop t (fun y => ρ y * odeKoop (-t) ψ y) x = ρ (mob t x) * ψ x := by sorry
