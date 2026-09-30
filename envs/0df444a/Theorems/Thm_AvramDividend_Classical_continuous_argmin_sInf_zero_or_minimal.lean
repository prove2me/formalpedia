-- Prove2me | Theorems.Thm_AvramDividend_Classical_continuous_argmin_sInf_zero_or_minimal
-- name    : AvramDividend.Classical.continuous_argmin_sInf_zero_or_minimal
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-30T00:04:51.90103+00:00
-- url     : https://prove2.me/theorems/7690ce9e-5748-4939-8720-527933ce7844
-- title:
--   The positive infimum of a continuous global-argmin set is zero or remains a minimiser
-- statement:
--   For a continuous real function on the positive half-line, let S be the set of positive global minimisers. If S is nonempty, then inf S is either zero or is itself a positive global minimiser. This is the pure closure-of-argmin step needed to identify c* with a derivative minimiser.
-- source:
--   Elementary real analysis: csInf_mem_closure for the positive argmin set, sequential characterization of closure in ℝ, and continuity of f on (0,∞).

import Mathlib

open Filter Set Topology

namespace AvramDividend.Classical

theorem continuous_argmin_sInf_zero_or_minimal (f : ℝ → ℝ)
    (hcont : ContinuousOn f (Ioi 0))
    (hne : {a : ℝ | 0 < a ∧ ∀ x : ℝ, 0 < x → f a ≤ f x}.Nonempty) :
    sInf {a : ℝ | 0 < a ∧ ∀ x : ℝ, 0 < x → f a ≤ f x} = 0 ∨
      (0 < sInf {a : ℝ | 0 < a ∧ ∀ x : ℝ, 0 < x → f a ≤ f x} ∧
        ∀ x : ℝ, 0 < x →
          f (sInf {a : ℝ | 0 < a ∧ ∀ y : ℝ, 0 < y → f a ≤ f y}) ≤ f x) := by sorry

end AvramDividend.Classical
