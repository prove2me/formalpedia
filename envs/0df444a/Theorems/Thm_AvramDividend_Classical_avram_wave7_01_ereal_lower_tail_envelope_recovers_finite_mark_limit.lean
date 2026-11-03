-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_01_ereal_lower_tail_envelope_recovers_finite_mark_limit
-- name    : AvramDividend.Classical.avram_wave7_01_ereal_lower_tail_envelope_recovers_finite_mark_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T17:46:21.232065+00:00
-- url     : https://prove2.me/theorems/b5d9db8e-e6f1-402b-9623-cfe2ff7bdd95
-- title:
--   Extended-real lower-tail envelope recovers every finite convergent jump mark
-- statement:
--   For an EReal sequence converging to a finite real value l, its countable tail lower envelope sup_m inf_{n≥m} a_n equals the finite EReal limit, so the globally defined toReal returns l. This is the exact recovery property needed to combine a measurable all-path raw-sample liminf with càdlàg one-sided mark convergence.
-- source:
--   Mathlib Filter.Tendsto.liminf_eq and Filter.liminf_eq_iSup_iInf_of_nat identify the tail envelope; EReal.toReal_coe recovers the real limit. No sample-space changes, no Levy intensity assumptions.

import Mathlib

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_01_ereal_lower_tail_envelope_recovers_finite_mark_limit
    (a : ℕ → EReal) (l : ℝ)
    (h : Tendsto a atTop (𝓝 (l : EReal))) :
    EReal.toReal (⨆ m : ℕ, ⨅ n : ℕ,
      if m ≤ n then a n else ⊤) = l := by sorry
