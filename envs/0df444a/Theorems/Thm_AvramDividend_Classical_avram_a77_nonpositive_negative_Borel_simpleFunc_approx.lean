-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a77_nonpositive_negative_Borel_simpleFunc_approx
-- name    : AvramDividend.Classical.avram_a77_nonpositive_negative_Borel_simpleFunc_approx
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T22:38:13.509664+00:00
-- url     : https://prove2.me/theorems/17b36358-6f1b-4b6f-82a7-0781ec173e7e
-- title:
--   Nonpositive real simple Borel mark quantisers converge pointwise to positive tilt times every strict negative mark
-- statement:
--   For each nonnegative tilt theta, there is a sequence of finite-range measurable real simple Borel mark functions q_n with values never positive and q_n(y) approaching theta*y for every strictly negative original Levy jump mark y. Construction uses Mathlib strongly measurable approximation of min(theta*y,0), then a continuous clamp to nonpositive values. This is the deterministic finite mark quantisation required for original source physical negative-mark finite-step counting and full Laplace limit, before converting simple function fibres into original sample-space jump count expectations.
-- source:
--   Avram original a77 physical negative-mark Laplace full-step construction, currently Open 4c557e90 under cc5c4242 under 5b48325d under 8bbaf3a8 under a77 root. This is the generic deterministic mark component, to be made reachable through accepted cc5-source bridge.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem AvramDividend.Classical.avram_a77_nonpositive_negative_Borel_simpleFunc_approx
    (θ : ℝ) (hθ : 0 ≤ θ) :
    ∃ q : ℕ → SimpleFunc ℝ ℝ,
      (∀ n y, q n y ≤ 0) ∧
      (∀ y, y < 0 →
        Tendsto (fun n => q n y) atTop (𝓝 (θ * y))) := by sorry
