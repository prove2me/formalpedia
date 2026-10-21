-- Prove2me | Theorems.Thm_CoProdBundle_Equil_feasible_pred
-- name    : CoProdBundle.Equil.feasible_pred
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:15:31.951677+00:00
-- url     : https://prove2.me/theorems/2bc88749-bc84-4381-b2db-418b543c8956
-- title:
--   Proof of Lemma 1, p. 30 — if i satisfies c_i ≤ (c_1+…+c_i)/(i−(1−3θ/2)) then so does i−1 (i ≥ 2); i = 1 always does
-- statement:
--   Let $I \ge 1$, let $0 < c_1 \le c_2 \le \dots \le c_I$, and let $0 < \theta < 2/3$. Call $k \in \{1,\dots,I\}$ *feasible* if
--   $$c_k \le \frac{c_1 + \dots + c_k}{k - (1 - 3\theta/2)}. \qquad (2a)$$
--   Then:
--   1. $k = 1$ is feasible;
--   2. if $k \ge 2$ is feasible, then $k - 1$ is feasible.
--
--   Hence the feasible indices are exactly $\{1, \dots, K\}$ with $K$ the largest feasible index, which is why the maximum in (2a) determines the set of participating producers.
--
--   **Formalization Note** The paper writes "$LHS(i-1) < LHS(i)$" and then proves the weak inequality; under equal costs only the weak one holds, and only the weak one is needed. Lean's producer `k - 1` is the paper's producer $k$.
-- source:
--   Bhargava, Bundling for Flexibility and Variety: An Economic Model for Multiproducer Value Aggregation, author's accepted manuscript (2020; Manag. Sci. doi:10.1287/mnsc.2020.3662), Appendix A.1, proof of Lemma 1, p. 30 (see also p. 17)

import Mathlib
import Definitions.Def_CoProdBundle_Equil_Setting

namespace CoProdBundle.Equil

/-- Proof of Lemma 1, p. 30 (and p. 17): the first producer satisfies the condition of (2a), and
if the page's producer `k ≥ 2` satisfies it then so does `k − 1`. -/
theorem feasible_pred (I : ℕ) (hI : 0 < I) (c : Fin I → ℝ) (hc0 : ∀ i, 0 < c i)
    (hcm : Monotone c) (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 2 / 3) :
    Feasible c θ 1 ∧ ∀ k : ℕ, 2 ≤ k → Feasible c θ k → Feasible c θ (k - 1) := by sorry

end CoProdBundle.Equil
