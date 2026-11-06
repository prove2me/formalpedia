-- Prove2me | Theorems.Thm_EthierKurtz_dissipative_resolvent_bound
-- name    : EthierKurtz.dissipative_resolvent_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T12:41:22.653534+00:00
-- url     : https://prove2.me/theorems/4b9e6aff-3622-48f3-8da1-849f2f82ff20
-- title:
--   Dissipative resolvent estimate for the martingale-problem operator
-- statement:
--   Let A be a dissipative linear relation on uniform bounded functions, in the Ethier-Kurtz sense that a * ||f|| <= ||a*f - g|| for every pair (f,g) in A and every a > 0. Then each fibre over A satisfies the resolvent bound ||f|| <= ||a*f - g|| / a. This is the elementary estimate from which the Hille-Yosida resolvent for the closure-range semigroup in the martingale characterization is built; applied through A' <= A it gives injectivity and the 1/a bound on the range operator.
-- source:
--   Isolates the one-line resolvent estimate used in the Ethier-Kurtz martingale-problem characterization (parent b1aead5f): from hdiss, divide by a > 0. The parent applies this through hsub to A' as the first step toward the contraction semigroup T on L. Provable from le_div_iff_0 with no martingale theory.

import Mathlib
import Definitions.Def_auto_M04_6e37b463_UniformBoundedFunction

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open EthierKurtz

theorem EthierKurtz.dissipative_resolvent_bound {E : Type*} (A : Submodule ℝ (UniformBoundedFunction E × UniformBoundedFunction E)) (hdiss : ∀ fg ∈ A, ∀ a : ℝ, 0 < a → a * ‖fg.1‖ ≤ ‖a • fg.1 - fg.2‖) (fg : UniformBoundedFunction E × UniformBoundedFunction E) (hfg : fg ∈ A) {a : ℝ} (ha : 0 < a) : ‖fg.1‖ ≤ ‖a • fg.1 - fg.2‖ / a := by
  sorry
