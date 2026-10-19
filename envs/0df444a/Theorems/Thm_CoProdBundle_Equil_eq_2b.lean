-- Prove2me | Theorems.Thm_CoProdBundle_Equil_eq_2b
-- name    : CoProdBundle.Equil.eq_2b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:15:34.404223+00:00
-- url     : https://prove2.me/theorems/141cf089-1238-4faa-915a-50baed26a950
-- title:
--   Proof of Lemma 1, p. 30 — (2c) is (5c) at K, and plugging (5b) into (4c) gives Q*_i of (2b)
-- statement:
--   Under the standing assumptions ($I \ge 1$ producers with costs $0 < c_1 \le \dots \le c_I$, $b > 0$, $A - bw > 0$, $0 < \theta < 2/3$, $0 < \gamma < 1$), let $K$ be given by (2a) and $Q^*$ by (2c). Then:
--   1. $Q^*$ equals the closed form (5c) for the first $K$ producers;
--   2. for each producer $i \le K$, the right side of (4c) at $Q = Q^*$ equals
--   $$Q^*_i = \Bigl[1 - c_i\,\frac{K - (1 - 3\theta/2)}{c_1 + \dots + c_K}\Bigr]\frac{2Q^*}{2 - 3\theta}. \qquad (2b)$$
--
--   This links the first-order conditions to the explicit outputs of Lemma 1.
--
--   **Formalization Note** Lean's producer `i` with `i < K` is the paper's producer $i+1 \le K$. The paper's $c$ in $A - bc$ is `w`.
-- source:
--   Bhargava, Bundling for Flexibility and Variety: An Economic Model for Multiproducer Value Aggregation, author's accepted manuscript (2020; Manag. Sci. doi:10.1287/mnsc.2020.3662), Appendix A.1, proof of Lemma 1, p. 30

import Mathlib
import Definitions.Def_CoProdBundle_Equil_Setting

namespace CoProdBundle.Equil

/-- Proof of Lemma 1, p. 30: the closed form (2c) is (5c) at `k = K`, and plugging it into (4c)
gives (2b) for each of the first `K` producers. -/
theorem eq_2b (I : ℕ) (hI : 0 < I) (c : Fin I → ℝ) (hc0 : ∀ i, 0 < c i)
    (hcm : Monotone c) (A b w θ γ : ℝ) (hb : 0 < b) (hAw : 0 < A - b * w) (hθ0 : 0 < θ)
    (hθ1 : θ < 2 / 3) (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    Qstar γ A b w θ c = Q5c γ A b w θ c (Kstar c θ) ∧
    ∀ i : Fin I, (i : ℕ) < Kstar c θ →
      br4c γ A b w θ (c i) (Qstar γ A b w θ c) = qstar γ A b w θ c i := by sorry

end CoProdBundle.Equil
