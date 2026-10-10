-- Prove2me | Theorems.Thm_BookProof_OdeUnitaryFlow_odeKoop_add
-- name    : BookProof.OdeUnitaryFlow.odeKoop_add
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T08:41:59.259982+00:00
-- url     : https://prove2.me/theorems/9fbeb92a-bbad-4180-836e-c48018b6a8aa
-- title:
--   `BookProof.OdeUnitaryFlow.odeKoop_add` (s t : ℝ) (ψ : ℝ → ℂ) (x : ℝ) (hs : 1 + s * x ≠ 0) (hst : 1 + (s + t) * x ≠ 0) : odeKoop s (odeKoop t ψ) x = odeKoop (s + t) ψ x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterOdeUnitaryFlow`.
--
--   `BookProof.OdeUnitaryFlow.odeKoop_add` (s t : ℝ) (ψ : ℝ → ℂ) (x : ℝ) (hs : 1 + s * x ≠ 0) (hst : 1 + (s + t) * x ≠ 0) : odeKoop s (odeKoop t ψ) x = odeKoop (s + t) ψ x
--
--   Formalization note: Lean 4 identifier `BookProof.OdeUnitaryFlow.odeKoop_add`.

-- Generated from ChapterOdeUnitaryFlow.lean — theorem BookProof.OdeUnitaryFlow.odeKoop_add
import Mathlib
import Definitions.Def_ChapterOdeUnitaryFlow
open BookProof.OdeUnitaryFlow



open MeasureTheory Filter Set
open scoped Topology ENNReal

theorem BookProof.OdeUnitaryFlow.odeKoop_add (s t : ℝ) (ψ : ℝ → ℂ) (x : ℝ) (hs : 1 + s * x ≠ 0)
    (hst : 1 + (s + t) * x ≠ 0) :
    odeKoop s (odeKoop t ψ) x = odeKoop (s + t) ψ x := by sorry
