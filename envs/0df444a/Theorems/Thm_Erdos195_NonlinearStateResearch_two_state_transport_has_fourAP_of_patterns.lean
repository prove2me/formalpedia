-- Prove2me | Theorems.Thm_Erdos195_NonlinearStateResearch_two_state_transport_has_fourAP_of_patterns
-- name    : Erdos195.NonlinearStateResearch.two_state_transport_has_fourAP_of_patterns
-- status  : Proved
-- author  : @xwh
-- created : 2026-10-23T09:57:07.942915+00:00
-- url     : https://prove2.me/theorems/97addb71-ee9e-4887-806d-588d491273f7
-- title:
--   Two-state binary-prefix transports under dyadic order patterns always contain a monotone four-term progression
-- statement:
--   Let p:ℕ≃ℕ be a permutation and write pos(m)=p⁻¹(m). Assume both of the following order conditions:
--
--   $$
--   \operatorname{pos}(0)<\operatorname{pos}(2^k)<\operatorname{pos}(2\cdot2^k)<\operatorname{pos}(m\cdot2^k)
--   \quad\text{for every }k\ge0,\ m\ge4,
--   $$
--
--   and
--
--   $$
--   \operatorname{pos}(3\cdot2^k)<\operatorname{pos}(2\cdot2^k)
--   <\operatorname{pos}((2n+1)\cdot2^k)<\operatorname{pos}(2n\cdot2^k)
--   \quad\text{for every }k\ge0,\ n\ge2.
--   $$
--
--   Let the state set consist of two Boolean values. Choose arbitrary integer coefficients a_s, arbitrary transitions δ₀,δ₁ between these two states, and an arbitrary initial state s. Define the binary-prefix value map by the exact terminating recursion
--
--   $$
--   G_s(0)=0,\qquad G_s(2n)=2G_{\delta_0(s)}(n),\qquad
--   G_s(2n+1)=2G_{\delta_1(s)}(n)+a_s.
--   $$
--
--   If f:ℕ≃ℤ satisfies f(i)=G_s(p(i)) for every i, then f contains a monotone four-term arithmetic progression in the original canonical sense. No oddness, sign, magnitude, transition, or reachability hypotheses are imposed.
--
--   The actual Ho permutation is a separately checked simultaneous instance of the two order conditions. This excludes a genuine nonlinear two-state construction family beyond global position-only coefficients. It makes no assertion about three or more states, general nonlinear transports, or the unresolved original Erdős195 existence problem.
-- source:
--   Independent two-state transport obstruction reconstructed in this research branch. The common-successor case uses the accepted original triangular-pattern theorem1f121ed8-0503-43b5-aefa-7fd7f04746ad. The actual Ho implementation from arXiv:2609.12780v1 is only a checked application; its first four entries, even-order self-similarity E6 and paired-odd guard E11 establish the displayed patterns. Neither these new helpers nor this obstruction is attributed to Ho's paper. No claim of global literature novelty or guaranteed citation is made.

import Mathlib
import Definitions.Def_Erdos195_defs
import Definitions.Def_Erdos195_TwoStateBinary_Model

namespace Erdos195.NonlinearStateResearch

theorem two_state_transport_has_fourAP_of_patterns
    (p : ℕ ≃ ℕ) (a : Bool → ℤ) (δ₀ δ₁ : Bool → Bool) (s : Bool)
    (f : ℕ ≃ ℤ)
    (hval : ∀ i, f i = stateValue a δ₀ δ₁ s (p i))
    (hTail : ∀ k m : ℕ, 4 ≤ m →
      p.symm (2^k*0) < p.symm (2^k*1) ∧
      p.symm (2^k*1) < p.symm (2^k*2) ∧
      p.symm (2^k*2) < p.symm (2^k*m))
    (hPattern : ∀ k n : ℕ, 2 ≤ n →
      p.symm (2^k*3) < p.symm (2^k*2) ∧
      p.symm (2^k*2) < p.symm (2^k*(2*n+1)) ∧
      p.symm (2^k*(2*n+1)) < p.symm (2^k*(2*n))) : HasMonotoneAP f 4 := by sorry

end Erdos195.NonlinearStateResearch
