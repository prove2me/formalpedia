-- Prove2me | Theorems.Thm_EtaQBridgePublished_finite_double_cosine_norm
-- name    : EtaQBridgePublished.finite_double_cosine_norm
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-16T07:14:02.653389+00:00
-- url     : https://prove2.me/theorems/271410bd-f8d2-4c76-ae7a-928fe6eefbe5
-- title:
--   Finite double cosine sum equals a complex squared modulus
-- statement:
--   For every finite index set and real weights and phases, the double cosine sum equals the squared modulus of the corresponding complex trigonometric sum. No convergence assumption. This is the finite algebraic origin of the Dirichlet-eta identity in the RH project.
-- source:
--   Desenvolvimento RH, Ricardo Marangoni Brandao Bueno. PF28 Part 97 C.9-C.10; Part 5.2-5.3; Branch2 Appendix B.1-B.5; RH Project Version 2 Sections 1-4. https://www.academia.edu/165637186/ . Lean translation 2026-11-16; classical identities, no novelty or RH-proof claim.

import Mathlib
open scoped BigOperators

theorem EtaQBridgePublished.finite_double_cosine_norm {ι : Type*} (s : Finset ι) (a θ : ι → ℝ) :
    (∑ i ∈ s, ∑ j ∈ s, a i * a j * Real.cos (θ i - θ j)) =
      Complex.normSq (∑ i ∈ s,
        (a i : ℂ) * ((Real.cos (θ i) : ℂ) + (Real.sin (θ i) : ℂ) * Complex.I)) := by sorry
