-- Prove2me | Theorems.Thm_CoProdBundle_Equil_eq_6_feasibility
-- name    : CoProdBundle.Equil.eq_6_feasibility
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:15:40.928233+00:00
-- url     : https://prove2.me/theorems/3f714ffc-46e6-4b8e-91b3-549de962326d
-- title:
--   (6), p. 17 — at the aggregate (5c) of producers 1…K, c_K ≤ γS(Q)/Q iff c_K ≤ c̄_K · K/(K − (1 − 3θ/2))
-- statement:
--   Under the standing assumptions ($I \ge 1$ producers with costs $0 < c_1 \le \dots \le c_I$, $b > 0$, $A - bw > 0$, $0 < \theta < 2/3$, $0 < \gamma < 1$), let $1 \le k \le I$, let $\bar c_k = (c_1+\dots+c_k)/k$, and let $Q_k$ be the closed-form aggregate (5c) of the first $k$ producers. Then the $k$-th producer satisfies the individual-rationality bound at $Q_k$ exactly when its cost satisfies (6):
--   $$c_k \le \frac{\gamma\,S(Q_k)}{Q_k} \iff c_k \le \frac{\bar c_k \cdot k}{k - (1 - 3\theta/2)}. \qquad (6)$$
--
--   Since $\bar c_k \cdot k = c_1 + \dots + c_k$, condition (6) is the condition of (2a); this is how the participation constraint of the last active producer becomes the explicit rule that determines $K$.
--
--   **Formalization Note** Lean's producer `j` is the paper's producer $k = j + 1$. The paper's $c$ in $A - bc$ is `w`.
-- source:
--   Bhargava, Bundling for Flexibility and Variety: An Economic Model for Multiproducer Value Aggregation, author's accepted manuscript (2020; Manag. Sci. doi:10.1287/mnsc.2020.3662), §4.2, (6), p. 17; Appendix A.1, proof of Lemma 1, p. 30

import Mathlib
import Definitions.Def_CoProdBundle_Equil_Setting

namespace CoProdBundle.Equil

/-- (6), p. 17: at the aggregate (5c) of the first `k` producers, the last of them meets the IR
bound `c_k ≤ γ S(Q)/Q` iff `c_k ≤ c̄_k · k/(k − (1 − 3θ/2))`. Lean's producer `j` is the page's
`k = j + 1`. -/
theorem eq_6_feasibility (I : ℕ) (hI : 0 < I) (c : Fin I → ℝ) (hc0 : ∀ i, 0 < c i)
    (hcm : Monotone c) (A b w θ γ : ℝ) (hb : 0 < b) (hAw : 0 < A - b * w) (hθ0 : 0 < θ)
    (hθ1 : θ < 2 / 3) (hγ0 : 0 < γ) (hγ1 : γ < 1) (j : Fin I) :
    c j ≤ γ * S A b w θ (Q5c γ A b w θ c ((j : ℕ) + 1)) / Q5c γ A b w θ c ((j : ℕ) + 1) ↔
      c j ≤ (psum c ((j : ℕ) + 1) / ((j : ℕ) + 1 : ℝ)) * ((j : ℕ) + 1 : ℝ) /
        (((j : ℕ) + 1 : ℝ) - alpha θ) := by sorry

end CoProdBundle.Equil
