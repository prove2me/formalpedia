-- Prove2me | Theorems.Thm_ActuarialValuation_finiteEntropicTransitionMoment_pos
-- name    : ActuarialValuation.finiteEntropicTransitionMoment_pos
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T09:36:03.338987+00:00
-- url     : https://prove2.me/theorems/c212b0b6-0e20-4b19-9b6c-a27c79228de0
-- title:
--   Normalised stochastic transitions give a positive exponential moment
-- statement:
--   A stochastic transition row has nonnegative entries adding to one; at least one entry is positive. Every real exponential of a finite real-valued loss is strictly positive, so the sum of these weighted exponentials is strictly positive. This remains valid for arbitrary real beta and gamma and for some zero-probability destination states.
--
--   **Mathematical statement**
--
--   $$
--   M_{\gamma,\beta}(s,a;F)>0
--   $$
-- source:
--   Bäuerle and Glauner (2022), Markov decision processes with recursive risk measures, European Journal of Operational Research 296(3), Definition 4.6, Theorem 4.7, equation (4.2), DOI https://doi.org/10.1016/j.ejor.2021.04.030; Bäuerle and Jaśkiewicz (2024), entropic certainty equivalent, Example 1(a), equation (2), DOI https://doi.org/10.1007/s00186-024-00857-0; derived finite-state discrete-time insurer cost specialisation

import Mathlib
import Definitions.Def_actuarial_finiteEntropicTransitionMoment

namespace ActuarialValuation

theorem finiteEntropicTransitionMoment_pos {S A : Type*} [Fintype S]
  (P : S → A → S → ℝ) (cost : S → A → S → ℝ)
  (beta gamma : ℝ) (next : S → ℝ) (s : S) (a : A)
  (hP : ∀ t, 0 ≤ P s a t)
  (hsum : (∑ t : S, P s a t) = 1) :
  0 < finiteEntropicTransitionMoment P cost beta gamma next s a := by sorry

end ActuarialValuation
