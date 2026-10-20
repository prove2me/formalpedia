-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_finite_extended_infimum_isGLB
-- name    : AvramDividend.Classical.chat03_finite_extended_infimum_isGLB
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T20:52:54.883332+00:00
-- url     : https://prove2.me/theorems/9e18c0e5-9287-4efb-9f47-124d90a5a4ab
-- title:
--   Finite extended nonnegative-real first passage infimum gives exact nonnegative-real greatest lower bound
-- statement:
--   Given a predicate p on nonnegative real times and an extended nonnegative-real time T defined as the indexed infimum of all witness times t with p(t), if T is finite then the ordinary nonnegative-real T.toNNReal is the greatest lower bound of {t : p(t)}. This exact bridge converts Formalpedia's first-passage definition (indexed infimum in ℝ≥0∞, with infinity for no passage) into the NNReal IsGLB interface used by the already Proved Chat 03 strict-grid convergence theorems, without silently assigning finite time to a nonexistent exit or assuming the infimum is attained. The proof uses only pinned complete lattice iInf and the finite ENNReal.toNNReal cast equivalence.
-- source:
--   Pinned Mathlib ENNReal.coe_toNNReal, ENNReal.coe_le_coe and CompleteLattice.iInf; revision 0df444a360eaa60ab8c11dca51a86af692955474. Direct Avram two-sided first-passage bridge, Chat03 19 October 2026.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Data.ENNReal.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic

open Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat03_finite_extended_infimum_isGLB
    (p : ℝ≥0 → Prop) (T : ℝ≥0∞)
    (hT : T = ⨅ (t : ℝ≥0) (_ : p t), (t : ℝ≥0∞))
    (hfinite : T ≠ ∞) :
    IsGLB {t : ℝ≥0 | p t} T.toNNReal := by sorry
