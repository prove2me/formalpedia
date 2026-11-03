-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_01_real_mark_sequence_liminf_extension_measurable
-- name    : AvramDividend.Classical.avram_wave7_01_real_mark_sequence_liminf_extension_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T17:44:41.377201+00:00
-- url     : https://prove2.me/theorems/4cf54147-c481-4f8a-b36a-579fb7a874e1
-- title:
--   Globally measurable extended-real lower-tail mark envelope for raw path samples
-- statement:
--   For any countable family of measurable real-valued raw coordinate-path samples, the lower-tail envelope formed as EReal liminf and mapped back to real by its globally defined toReal is measurable on the entire coordinate product sigma-algebra. At paths where the samples converge to a finite real mark, a separate order-limit identity recovers that exact mark. This avoids assuming a pointwise limit on non-cadlag paths.
-- source:
--   Use Mathlib measurable_coe_real_ereal, Measurable.iInf, Measurable.iSup, and Measurable.ereal_toReal. Each conditional finite-index sample is measurable, and countable lattice sup/inf preserve measurability in EReal.

import Mathlib

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_01_real_mark_sequence_liminf_extension_measurable
    (f : ℕ → (ℝ≥0 → ℝ) → ℝ)
    (hf : ∀ n : ℕ, Measurable (f n)) :
    Measurable (fun Y : ℝ≥0 → ℝ =>
      EReal.toReal (⨆ m : ℕ, ⨅ n : ℕ,
        if m ≤ n then (f n Y : EReal) else ⊤)) := by sorry
