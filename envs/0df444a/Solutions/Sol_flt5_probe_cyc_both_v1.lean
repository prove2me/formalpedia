-- Prove2me | solution 1 for flt5_probe_cyc_both_v1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-17T02:42:46.655891+00:00
-- url     : https://prove2.me/submissions/4bd868fb-f13d-4f54-afcd-47aca97f592e

import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots

theorem solution : ∃ ζ : CyclotomicField 5 ℚ, IsPrimitiveRoot ζ 5 ∧ True := by
  haveI : IsCyclotomicExtension ({5} : Set ℕ) ℚ (CyclotomicField 5 ℚ) :=
    CyclotomicField.isCyclotomicExtension 5 ℚ
  exact ⟨IsCyclotomicExtension.zeta 5 ℚ (CyclotomicField 5 ℚ),
    IsCyclotomicExtension.zeta_spec 5 ℚ (CyclotomicField 5 ℚ), trivial⟩
