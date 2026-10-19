-- Prove2me | Theorems.Thm_CoProdBundle_Equil_eq_4e
-- name    : CoProdBundle.Equil.eq_4e
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:15:34.78568+00:00
-- url     : https://prove2.me/theorems/3ef1a13f-6bf3-479d-8432-e4fa23303a7e
-- title:
--   (4e), p. 16 — the solution of (4c) is nonnegative iff c_i ≤ (2γ/(bQ^{(2−3θ)/2}))((A−bc)/3)^{3/2} = γS(Q)/Q
-- statement:
--   Under the standing assumptions ($b > 0$, $A - bw > 0$, $0 < \theta < 2/3$, $0 < \gamma < 1$, costs $0 < c_1 \le \dots \le c_I$), let $Q > 0$ and let $i$ be a producer. Write
--   $$B(Q) = \frac{2\gamma}{b\,Q^{(2-3\theta)/2}}\Bigl(\frac{A-bw}{3}\Bigr)^{3/2}.$$
--   Then:
--   1. the right side of (4c) at $Q$ is nonnegative if and only if $c_i \le B(Q)$ (this is (4e));
--   2. $B(Q) = \gamma S(Q)/Q$, the producers' average revenue per value unit.
--
--   Part 2 identifies the bound of (4e) with the individual-rationality threshold "average revenue exceeds average cost" of §3.3.
--
--   **Formalization Note** "$Q_i \ge 0$" of (4e) is read as nonnegativity of the right side of (4c), the formula the paper calls $Q_i$. The paper's $c$ in $A - bc$ is `w`.
-- source:
--   Bhargava, Bundling for Flexibility and Variety: An Economic Model for Multiproducer Value Aggregation, author's accepted manuscript (2020; Manag. Sci. doi:10.1287/mnsc.2020.3662), §4.2, (4e), p. 16

import Mathlib
import Definitions.Def_CoProdBundle_Equil_Setting

namespace CoProdBundle.Equil

/-- (4e), p. 16: the solution (4c) is nonnegative iff
`c_i ≤ (2γ/(b Q^{(2−3θ)/2}))((A − b w)/3)^{3/2}`, and this bound is the average revenue `γ S(Q)/Q`. -/
theorem eq_4e (I : ℕ) (hI : 0 < I) (c : Fin I → ℝ) (hc0 : ∀ i, 0 < c i)
    (hcm : Monotone c) (A b w θ γ : ℝ) (hb : 0 < b) (hAw : 0 < A - b * w) (hθ0 : 0 < θ)
    (hθ1 : θ < 2 / 3) (hγ0 : 0 < γ) (hγ1 : γ < 1) (Q : ℝ) (hQ : 0 < Q) (i : Fin I) :
    (0 ≤ br4c γ A b w θ (c i) Q ↔
      c i ≤ 2 * γ / (b * Q ^ ((2 - 3 * θ) / 2)) * ((A - b * w) / 3) ^ (3 / 2 : ℝ)) ∧
    2 * γ / (b * Q ^ ((2 - 3 * θ) / 2)) * ((A - b * w) / 3) ^ (3 / 2 : ℝ) =
      γ * S A b w θ Q / Q := by sorry

end CoProdBundle.Equil
