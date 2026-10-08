-- Prove2me | Theorems.Thm_DemandSubstitution_Comparison_proposition1_central_foc
-- name    : DemandSubstitution.Comparison.proposition1_central_foc
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:12:41.669972+00:00
-- url     : https://prove2.me/theorems/865245bb-c555-465c-bc2a-99598972f29c
-- title:
--   Proposition 1, p. 5 — optimality condition (7) of the centralized problem at an interior optimal Q^c_i
-- statement:
--   In the $n$-product substitution model with a demand law $\mu$, let $Q^c$ be an optimal centralized stocking vector: $Q^c \ge 0$ maximizes the centralized expected profit over all nonnegative stocking vectors. Let $D^s_j = D_j + \sum_{k\ne j} a_{kj}(D_k - Q^c_k)^+$. Then for every product $i$ with $Q^c_i > 0$,
--   $$
--   \Pr(D_i < Q^c_i) - \Pr(D_i < Q^c_i < D^s_i) + \sum_{j \ne i} \frac{u_j + o_j}{u_i + o_i}\, a_{ij}\, \Pr\big(D^s_j < Q^c_j,\ D_i > Q^c_i\big) = \frac{u_i}{u_i + o_i}. \tag{7}
--   $$
--
--   Without the second and third terms this is the classical newsvendor critical-fractile condition. The second term raises the stocking level of product $i$ for the substitute demand it receives; the third term lowers it because a stock-out of product $i$ may be recovered as a sale of another product.
--
--   **Formalization Note** The hypothesis $Q^c_i > 0$ is a disclosed pin: (7) is an equality only at an interior optimum, and a product may be optimally left unstocked when substitution covers its demand (the paper states (7) for every $i$ without this proviso). The optimum is a maximizer of the profit; (7) is a conclusion, not part of the definition.
-- source:
--   Netessine & Rudi, Centralized and Competitive Inventory Models with Demand Substitution, SSRN 303779 (Simon School Working Paper OP 02-01, April 2002), p. 5, Proposition 1, equation (7)

import Mathlib
import Definitions.Def_DemandSubstitution_Comparison_Setting

open MeasureTheory

namespace DemandSubstitution.Comparison

/-- Proposition 1, p. 5: at an optimal centralized stocking vector `Q^c`, for every product `i`
stocked in positive quantity, condition (7) holds:
`Pr(D_i < Q^c_i) − P(D_i < Q^c_i < D^s_i) + ∑_{j≠i} (u_j + o_j)/(u_i + o_i) a_ij
  Pr(D^s_j < Q^c_j, D_i > Q^c_i) = u_i/(u_i + o_i)`, every `D^s` evaluated at `Q^c`.
The hypothesis `0 < Qc i` (interior optimum) is a disclosed pin. -/
theorem proposition1_central_foc {n : ℕ} (M : Model n) (μ : Measure (Fin n → ℝ))
    [IsProbabilityMeasure μ] (hμ : DemandSubstitution.Competitive.IsDemandLaw μ) (Qc : Fin n → ℝ)
    (hc : IsCentralOptimal M μ Qc) (i : Fin n) (hi : 0 < Qc i) :
    μ.real {x | x i < Qc i} - μ.real {x | x i < Qc i ∧ Qc i < Ds M Qc x i}
      + ∑ j ∈ Finset.univ.erase i,
          (M.u j + M.o j) / (M.u i + M.o i) * M.a i j
            * μ.real {x | Ds M Qc x j < Qc j ∧ Qc i < x i}
      = M.u i / (M.u i + M.o i) := by sorry

end DemandSubstitution.Comparison
