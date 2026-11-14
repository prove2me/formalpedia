-- Prove2me | Theorems.Thm_APFPaper5_K1_iterated_turn_in_plane
-- name    : APFPaper5.K1.iterated_turn_in_plane
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:32:39.828585+00:00
-- url     : https://prove2.me/theorems/aeeb352b-aef6-4431-9393-25311bf5f409
-- title:
--   A second-order linear recurrence confines every iterate to two generators
-- statement:
--   Let T act on a real vector space. Assume hTadd: T is additive, hTsmul: T is real-homogeneous, and hfirst: T²z=αz+βTz for supplied z,α,β. Then for every natural n there are real a,b such that Tⁿz=az+bTz. This is containment in the span of z and Tz, whose dimension may be zero, one or two. It proves neither independence nor exactly three directions after adjoining another vector, and does not establish a bridge to physical space or first-jet completeness.
-- source:
--   Sib v15 frozen source: Theorems/Thm_APFPaper5_K1_three_directions.lean:46; Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex, 1621-1647; C:/Users/brook/Dev/apf-codebase/apf/_held_holonomy_linear.py, 125-232; Artifacts_2026-11-12_session/claude/EthanBrooke-01WrrBvu/RULING_three_yeses_2026-11-12.md, 1-2 and standing

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Module.Defs
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option autoImplicit false
namespace APFPaper5.K1
end APFPaper5.K1
open APFPaper5.K1
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

theorem APFPaper5.K1.iterated_turn_in_plane (T : V → V)
    (hTadd : ∀ a b : V, T (a + b) = T a + T b)
    (hTsmul : ∀ (r : ℝ) (a : V), T (r • a) = r • T a)
    (z : V) (alpha beta : ℝ) (hfirst : T (T z) = alpha • z + beta • T z) :
    ∀ n : ℕ, ∃ a b : ℝ, T^[n] z = a • z + b • T z := by sorry
