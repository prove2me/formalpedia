-- Prove2me | solution 1 for syracuse_primitive_word_ge_6956_rotated_baseline_2786502_iff_no_minimal_period_ge_6956_cycle
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-07T13:29:28.38085+00:00
-- url     : https://prove2.me/submissions/71bf1d52-b220-48c3-a397-31542baaa171

import Mathlib.Dynamics.PeriodicPts.Defs
import Definitions.Def_syracuseStep
import Definitions.Def_syracuseOffsetMod
import Theorems.Thm_syracuse_cycle_eq_one_of_primitive_word_ge_6956_rotated_baseline_2786502
import Theorems.Thm_syracuse_primitive_word_ge_6956_rotated_baseline_2786502_of_no_cycle

/-
  Attribution: new; no code reused from other users' submissions. It only combines the
  forward and reverse bridge theorems of this packet.
-/

set_option autoImplicit false

theorem solution :
    (∀ w : List ℕ,
      (∀ a ∈ w, 0 < a) →
      6956 ≤ w.length →
      (∀ d : ℕ, 0 < d → d < w.length → w.rotate d ≠ w) →
      3 ^ w.length < 2 ^ w.sum →
      200 * w.sum < 317 * w.length →
      306 * w.sum < 485 * w.length →
      (2 : ℕ) ^ w.sum * (2310000 : ℕ) ^ w.length ≤ (3 * 2310000 + 1 : ℕ) ^ w.length →
      (∀ d : ℕ, d < w.length →
        (2786502 : ℕ) * (2 ^ w.sum - 3 ^ w.length) ≤ syracuseAffineConstant (w.rotate d)) →
      ¬(2 ^ w.sum - 3 ^ w.length) ∣ syracuseAffineConstant w) ↔
    (∀ m p : ℕ, 0 < m → 6956 ≤ p →
      Function.minimalPeriod syracuseStep m = p → m = 1) := by
  constructor
  · intro hleaf m p hm hp hq
    have hp0 : 0 < p := by omega
    have hcyc : syracuseStep^[p] m = m := by
      rw [← hq]
      exact Function.isPeriodicPt_minimalPeriod syracuseStep m
    exact syracuse_cycle_eq_one_of_primitive_word_ge_6956_rotated_baseline_2786502
      hleaf m p hm hp0 hcyc
  · intro hnocycle w hpositive hlength hprimitive hgap hlow hlowSharp hbaselineBudget
      hrotatedBaseline
    exact syracuse_primitive_word_ge_6956_rotated_baseline_2786502_of_no_cycle
      hnocycle w hpositive hlength hprimitive hgap hlow hlowSharp hbaselineBudget
      hrotatedBaseline
