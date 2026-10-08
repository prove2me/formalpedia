-- Prove2me | Theorems.Thm_DemandSubstitution_Comparison_eq8_partial_derivative
-- name    : DemandSubstitution.Comparison.eq8_partial_derivative
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:12:48.054173+00:00
-- url     : https://prove2.me/theorems/36e4eadc-1459-4dcf-8dfe-a04ad772e1cf
-- title:
--   Equation (8), p. 6 — the partial derivative ∂π/∂Q_i of the centralized expected profit
-- statement:
--   In the $n$-product substitution model with a demand law $\mu$, fix a stocking vector $Q$ and a product $i$, and let every $D^s_j = D_j + \sum_{k\ne j} a_{kj}(D_k - Q_k)^+$ be evaluated at $Q$. The centralized expected profit $\pi$, viewed as a function of the $i$-th stocking quantity with the others held fixed, is differentiable at $Q_i$ and
--   $$
--   \begin{aligned}
--   \frac{\partial \pi}{\partial Q_i} = {} & -\sum_{j\ne i} u_j a_{ij} \Pr(D_i > Q_i) + \big[u_i \Pr(D^s_i > Q_i) - o_i \Pr(D^s_i < Q_i)\big] \\
--   & + \sum_{j \ne i} \big[u_j a_{ij} \Pr(D^s_j > Q_j,\ D_i > Q_i) - o_j a_{ij} \Pr(D^s_j < Q_j,\ D_i > Q_i)\big].
--   \end{aligned} \tag{8}
--   $$
--
--   The first sum is the loss of perfect-information profit of the other products when product $i$ is restocked, the bracket is the usual newsvendor marginal value of product $i$, and the last sum accounts for the substitute demand that product $i$ stops sending to the other products. Setting (8) to zero yields the centralized optimality condition (7).
--
--   **Formalization Note** The derivative is two-sided (`HasDerivAt`) and is stated for every real vector $Q$; $\pi$ is the three-part profit of the setting.
-- source:
--   Netessine & Rudi, Centralized and Competitive Inventory Models with Demand Substitution, SSRN 303779 (Simon School Working Paper OP 02-01, April 2002), p. 6, proof of Proposition 1, equation (8)

import Mathlib
import Definitions.Def_DemandSubstitution_Comparison_Setting

open MeasureTheory

namespace DemandSubstitution.Comparison

/-- Equation (8), p. 6: the partial derivative of the centralized expected profit with respect to
`Q_i`,
`∂π/∂Q_i = −∑_{j≠i} u_j a_ij Pr(D_i > Q_i) + [u_i Pr(D^s_i > Q_i) − o_i Pr(D^s_i < Q_i)]
  + ∑_{j≠i} [u_j a_ij Pr(D^s_j > Q_j, D_i > Q_i) − o_j a_ij Pr(D^s_j < Q_j, D_i > Q_i)]`,
as a two-sided derivative in the `i`-th coordinate, every `D^s` evaluated at `Q`. -/
theorem eq8_partial_derivative {n : ℕ} (M : Model n) (μ : Measure (Fin n → ℝ))
    [IsProbabilityMeasure μ] (hμ : DemandSubstitution.Competitive.IsDemandLaw μ) (Q : Fin n → ℝ) (i : Fin n) :
    HasDerivAt (fun q : ℝ => centralProfit M μ (Function.update Q i q))
      (-(∑ j ∈ Finset.univ.erase i, M.u j * M.a i j * μ.real {x | Q i < x i})
        + (M.u i * μ.real {x | Q i < Ds M Q x i} - M.o i * μ.real {x | Ds M Q x i < Q i})
        + ∑ j ∈ Finset.univ.erase i,
            (M.u j * M.a i j * μ.real {x | Q j < Ds M Q x j ∧ Q i < x i}
              - M.o j * M.a i j * μ.real {x | Ds M Q x j < Q j ∧ Q i < x i}))
      (Q i) := by sorry

end DemandSubstitution.Comparison
