-- Prove2me | Theorems.Thm_DemandSubstitution_Comparison_deriv_substitute_shortage
-- name    : DemandSubstitution.Comparison.deriv_substitute_shortage
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:12:29.653459+00:00
-- url     : https://prove2.me/theorems/8dbf412d-83a2-443c-ac9c-cc9bf17fe252
-- title:
--   Proof of Proposition 1, p. 6 — ∂E(D^s_j − Q_j)⁺/∂Q_i = −a_ij Pr(D^s_j > Q_j, D_i > Q_i) for j ≠ i
-- statement:
--   In the $n$-product substitution model with a demand law $\mu$ (absolutely continuous, concentrated on the positive orthant, integrable coordinates), fix a stocking vector $Q$ and two distinct products $j \ne i$. Consider the expected shortage of product $j$,
--   $$g(q) = \mathbb E\big(D^s_j - Q_j\big)^+,\qquad D^s_j = D_j + \sum_{k\ne j} a_{kj}(D_k - Q_k)^+ ,$$
--   as a function of the stocking quantity $q$ of product $i$ (substituted for $Q_i$ in $D^s_j$), all other quantities, including $Q_j$, held fixed. Then $g$ is differentiable at $q = Q_i$ and
--   $$\frac{\partial\, \mathbb E(D^s_j - Q_j)^+}{\partial Q_i} = -a_{ij}\,\Pr\big(D^s_j > Q_j,\ D_i > Q_i\big),$$
--   with $D^s_j$ evaluated at $Q$.
--
--   Raising the stock of product $i$ diverts substitute demand away from product $j$ exactly on the event where product $i$ is short and product $j$ is short too. This derivative is the building block of the centralized partial derivative (8).
--
--   **Formalization Note** The derivative is two-sided (`HasDerivAt`), matching the paper's $\lim_{\varepsilon\to0}$ with no side. The statement holds for every real vector $Q$.
-- source:
--   Netessine & Rudi, Centralized and Competitive Inventory Models with Demand Substitution, SSRN 303779 (Simon School Working Paper OP 02-01, April 2002), p. 6, proof of Proposition 1, display after "We then obtain"

import Mathlib
import Definitions.Def_DemandSubstitution_Comparison_Setting

open MeasureTheory

namespace DemandSubstitution.Comparison

/-- Proof of Proposition 1, p. 6: for `j ≠ i`,
`∂E(D^s_j − Q_j)⁺/∂Q_i = −a_ij Pr(D^s_j > Q_j, D_i > Q_i)`, as a two-sided derivative in the
`i`-th stocking quantity with all other stocking quantities (in particular `Q_j`) held fixed. -/
theorem deriv_substitute_shortage {n : ℕ} (M : Model n) (μ : Measure (Fin n → ℝ))
    [IsProbabilityMeasure μ] (hμ : DemandSubstitution.Competitive.IsDemandLaw μ) (Q : Fin n → ℝ) (i j : Fin n) (hji : j ≠ i) :
    HasDerivAt (fun q : ℝ => ∫ x, max (Ds M (Function.update Q i q) x j - Q j) 0 ∂μ)
      (-(M.a i j) * μ.real {x | Q j < Ds M Q x j ∧ Q i < x i}) (Q i) := by sorry

end DemandSubstitution.Comparison
