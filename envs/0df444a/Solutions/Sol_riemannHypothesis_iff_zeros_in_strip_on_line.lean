-- Prove2me | solution 1 for riemannHypothesis_iff_zeros_in_strip_on_line
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-08T16:13:14.823227+00:00
-- url     : https://prove2.me/submissions/7e901349-4f1f-4b9f-8004-8accd4ea26c8

import Theorems.Thm_Kawahira_nontrivial_zero_mem_strip
import Mathlib.NumberTheory.LSeries.Nonvanishing
set_option autoImplicit false
open Complex

theorem solution :
    RiemannHypothesis ↔
      ∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 → s.re = 1 / 2 := by
  constructor
  · intro h s hz hlower hupper
    apply h s hz
    · rintro ⟨n, hn⟩
      rw [hn] at hlower
      norm_num at hlower
      nlinarith
    · intro hn
      simp [hn] at hupper
  · intro h s hz htriv _
    have hb := Kawahira.nontrivial_zero_mem_strip s hz (by
      intro n hn
      exact htriv ⟨n, hn⟩)
    exact h s hz hb.1 hb.2
