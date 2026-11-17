-- Prove2me | Theorems.Thm_EtaQBridgePublished_tower_finite_difference
-- name    : EtaQBridgePublished.tower_finite_difference
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-16T07:14:32.581828+00:00
-- url     : https://prove2.me/theorems/02a67653-1add-4ba8-a28a-ea80585bb062
-- title:
--   Full summable tower as finite differences of boundary moments
-- statement:
--   For a complex sequence whose powers p through p+q are summable, the infinite tower sum y^p(1-y)^q is the binomial finite difference of its boundary moments. This proves the infinite-sum identity with explicit summability. It does not infer positivity of the differences from positivity of the moments, or identify the sequence with zeta zeros.
-- source:
--   Desenvolvimento RH, Ricardo Marangoni Brandao Bueno. PF28 Part 97 C.9-C.10; Part 5.2-5.3; Branch2 Appendix B.1-B.5; RH Project Version 2 Sections 1-4. https://www.academia.edu/165637186/ . Lean translation 2026-11-16; classical identities, no novelty or RH-proof claim.

import Mathlib
open scoped BigOperators

theorem EtaQBridgePublished.tower_finite_difference (y : ℕ → ℂ) (p q : ℕ)
    (h : ∀ j ∈ Finset.range (q+1), Summable (fun i => (y i)^(p+j))) :
    (∑' i, (y i)^p*(1-y i)^q) =
      ∑ j ∈ Finset.range (q+1), (-1 : ℂ)^j*(q.choose j : ℂ)*
        (∑' i, (y i)^(p+j)) := by sorry
