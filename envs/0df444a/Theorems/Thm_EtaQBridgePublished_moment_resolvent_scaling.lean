-- Prove2me | Theorems.Thm_EtaQBridgePublished_moment_resolvent_scaling
-- name    : EtaQBridgePublished.moment_resolvent_scaling
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-16T07:14:38.388725+00:00
-- url     : https://prove2.me/theorems/8ff3c060-b4ff-4fba-8f03-a4b52c24a03a
-- title:
--   Exact normalization between resolvent moments and tower boundary
-- statement:
--   The real-part moment of y_i=u squared/(u squared+B_i) equals u^(2n) times the real-part inverse-power sum. This is an identity for Lean tsum, including its conventional value for nonsummable functions. Analytic use for the zeta spectrum additionally needs summability; no convergence claim is made here.
-- source:
--   Desenvolvimento RH, Ricardo Marangoni Brandao Bueno. PF28 Part 97 C.9-C.10; Part 5.2-5.3; Branch2 Appendix B.1-B.5; RH Project Version 2 Sections 1-4. https://www.academia.edu/165637186/ . Lean translation 2026-11-16; classical identities, no novelty or RH-proof claim.

import Mathlib
open scoped BigOperators

theorem EtaQBridgePublished.moment_resolvent_scaling (B : ℕ → ℂ) (u : ℝ) (n : ℕ) :
    (∑' i, (((u : ℂ)^2/((u : ℂ)^2+B i))^n).re) =
      u^(2*n)*(∑' i, ((((u : ℂ)^2+B i)⁻¹)^n).re) := by sorry
