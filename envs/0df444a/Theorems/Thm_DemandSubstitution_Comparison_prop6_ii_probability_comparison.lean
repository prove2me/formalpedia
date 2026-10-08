-- Prove2me | Theorems.Thm_DemandSubstitution_Comparison_prop6_ii_probability_comparison
-- name    : DemandSubstitution.Comparison.prop6_ii_probability_comparison
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:12:22.328834+00:00
-- url     : https://prove2.me/theorems/98b2ca01-c6a7-4c36-9668-15d2199a6ddc
-- title:
--   Proof of Proposition 6(ii), p. 11 — Pr(D^sc_i < Q^c_i) ≤ Pr(D^sd_i < Q^d_i)
-- statement:
--   In the $n$-product substitution model with a demand law $\mu$, let $Q^c$ be an optimal centralized stocking vector and $Q^d$ a Nash equilibrium of the competitive game. Write
--   $$D^{sc}_i = D_i + \sum_{j\ne i} a_{ji}(D_j - Q^c_j)^+,\qquad D^{sd}_i = D_i + \sum_{j\ne i} a_{ji}(D_j - Q^d_j)^+$$
--   for the demand with substitution under the centralized and the competitive stocking vectors. Then for every product $i$ with $Q^c_i > 0$,
--   $$\Pr\big(D^{sc}_i < Q^c_i\big) \le \Pr\big(D^{sd}_i < Q^d_i\big).$$
--
--   The centralized first-order condition puts $\Pr(D^{sc}_i < Q^c_i)$ below the critical ratio $u_i/(u_i+o_i)$, while the equilibrium condition puts $\Pr(D^{sd}_i < Q^d_i)$ at it. This comparison is the core of the proof that competition stocks at least one product no less than centralized management.
--
--   **Formalization Note** The hypothesis $Q^c_i > 0$ is the interior-optimum pin inherited from Proposition 1. No positive density is assumed here.
-- source:
--   Netessine & Rudi, Centralized and Competitive Inventory Models with Demand Substitution, SSRN 303779 (Simon School Working Paper OP 02-01, April 2002), p. 11, proof of Proposition 6(ii), display after "it is easy to see that"

import Mathlib
import Definitions.Def_DemandSubstitution_Comparison_Setting

open MeasureTheory

namespace DemandSubstitution.Comparison

/-- Proof of Proposition 6(ii), p. 11: if `Q^c` is an optimal centralized stocking vector and
`Q^d` a Nash equilibrium of the competitive game, then for every product `i` with `Q^c_i > 0`,
`Pr(D^{sc}_i < Q^c_i) ≤ Pr(D^{sd}_i < Q^d_i)`, where `D^{sc}` and `D^{sd}` are `D^s` at `Q^c`
and at `Q^d`. -/
theorem prop6_ii_probability_comparison {n : ℕ} (M : Model n) (μ : Measure (Fin n → ℝ))
    [IsProbabilityMeasure μ] (hμ : DemandSubstitution.Competitive.IsDemandLaw μ) (Qc Qd : Fin n → ℝ)
    (hc : IsCentralOptimal M μ Qc) (hd : IsNash M μ Qd) (i : Fin n) (hi : 0 < Qc i) :
    μ.real {x | Ds M Qc x i < Qc i} ≤ μ.real {x | Ds M Qd x i < Qd i} := by sorry

end DemandSubstitution.Comparison
