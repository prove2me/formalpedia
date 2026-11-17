-- Prove2me | Theorems.Thm_EtaQBridgePublished_square_cutoff_limit
-- name    : EtaQBridgePublished.square_cutoff_limit
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-16T07:14:16.25342+00:00
-- url     : https://prove2.me/theorems/295c130c-a4da-49a4-a3e2-14ba7492f9c9
-- title:
--   Square-cutoff limit of a double cosine sum
-- statement:
--   If the ordered real and imaginary trigonometric partial sums converge to A and B, the square-cutoff double cosine sums converge to A squared plus B squared. The two Tendsto assumptions are explicit. This theorem does not establish convergence or identify the limits for the Dirichlet eta series.
-- source:
--   Desenvolvimento RH, Ricardo Marangoni Brandao Bueno. PF28 Part 97 C.9-C.10; Part 5.2-5.3; Branch2 Appendix B.1-B.5; RH Project Version 2 Sections 1-4. https://www.academia.edu/165637186/ . Lean translation 2026-11-16; classical identities, no novelty or RH-proof claim.

import Mathlib
open scoped BigOperators

theorem EtaQBridgePublished.square_cutoff_limit (a θ : ℕ → ℝ) (A B : ℝ)
    (hc : Filter.Tendsto (fun N => ∑ i ∈ Finset.range N, a i * Real.cos (θ i)) Filter.atTop (nhds A))
    (hs : Filter.Tendsto (fun N => ∑ i ∈ Finset.range N, a i * Real.sin (θ i)) Filter.atTop (nhds B)) :
    Filter.Tendsto (fun N => ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
      a i * a j * Real.cos (θ i - θ j)) Filter.atTop (nhds (A^2+B^2)) := by sorry
