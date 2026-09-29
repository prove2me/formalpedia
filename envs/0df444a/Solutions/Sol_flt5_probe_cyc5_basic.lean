-- Prove2me | solution 1 for flt5_probe_cyc5_basic
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-17T02:42:46.994443+00:00
-- url     : https://prove2.me/submissions/c25b8fb7-7256-4dcc-afde-dce4b5c0980c

import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots

theorem solution : ∃ ζ : CyclotomicField 5 ℚ, IsPrimitiveRoot ζ 5 := by
  haveI : IsCyclotomicExtension ({5} : Set ℕ) ℚ (CyclotomicField 5 ℚ) :=
    CyclotomicField.isCyclotomicExtension 5 ℚ
  exact ⟨IsCyclotomicExtension.zeta 5 ℚ (CyclotomicField 5 ℚ),
    IsCyclotomicExtension.zeta_spec 5 ℚ (CyclotomicField 5 ℚ)⟩
