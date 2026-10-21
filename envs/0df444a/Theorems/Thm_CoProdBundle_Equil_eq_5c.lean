-- Prove2me | Theorems.Thm_CoProdBundle_Equil_eq_5c
-- name    : CoProdBundle.Equil.eq_5c
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:15:52.89685+00:00
-- url     : https://prove2.me/theorems/361f9b04-b2da-4f23-9afd-853cfe1e6b81
-- title:
--   (5a)–(5c), p. 17 — summing (4c) over the first K producers pins Q* = [(γ/(bc̄_K))(2 − (2−3θ)/K)]^{2/(2−3θ)}((A−bc)/3)^{3/(2−3θ)}
-- statement:
--   Under the standing assumptions ($I \ge 1$ producers with costs $0 < c_1 \le \dots \le c_I$, $b > 0$, $A - bw > 0$, $0 < \theta < 2/3$, $0 < \gamma < 1$), let $1 \le k \le I$, let $\bar c_k = (c_1 + \dots + c_k)/k$ be the average cost of the first $k$ producers, and let $Q > 0$. Write $F_i(Q)$ for the right side of (4c) for producer $i$. The following are equivalent:
--   1. $Q = \sum_{i=1}^{k} F_i(Q)$, i.e. the outputs (4c) of the first $k$ producers add up to $Q$ (5a);
--   2. $Q\Bigl(\dfrac{1}{Q^\theta}\,\dfrac{3}{A-bw}\Bigr)^{3/2} = \dfrac{\gamma}{b\bar c_k}\Bigl(2 - \dfrac{2-3\theta}{k}\Bigr)$ (5b);
--   3. $$Q = \Bigl[\frac{\gamma}{b\bar c_k}\Bigl(2 - \frac{2-3\theta}{k}\Bigr)\Bigr]^{2/(2-3\theta)}\Bigl(\frac{A-bw}{3}\Bigr)^{3/(2-3\theta)}. \qquad (5c)$$
--
--   This turns the implicit system of first-order conditions into a closed form for the aggregate output once the number of active producers is known.
--
--   **Formalization Note** The paper writes "$\bar c_{(K)} = \sum_i c_i$ denote the average"; the average, $(c_1+\dots+c_k)/k$, is what (5a) requires and is used here. The statement is (1)⇔(2) and (1)⇔(3). The paper's $c$ in $A - bc$ is `w`.
-- source:
--   Bhargava, Bundling for Flexibility and Variety: An Economic Model for Multiproducer Value Aggregation, author's accepted manuscript (2020; Manag. Sci. doi:10.1287/mnsc.2020.3662), §4.2, (5a)–(5c), p. 17

import Mathlib
import Definitions.Def_CoProdBundle_Equil_Setting

namespace CoProdBundle.Equil

/-- (5a)–(5c), p. 17: summing (4c) over the first `k` producers, the aggregate `Q` is a fixed
point iff (5b) holds iff `Q` equals the closed form (5c), with `c̄_k = (c_1 + … + c_k)/k`. -/
theorem eq_5c (I : ℕ) (hI : 0 < I) (c : Fin I → ℝ) (hc0 : ∀ i, 0 < c i)
    (hcm : Monotone c) (A b w θ γ : ℝ) (hb : 0 < b) (hAw : 0 < A - b * w) (hθ0 : 0 < θ)
    (hθ1 : θ < 2 / 3) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (k : ℕ) (hk1 : 1 ≤ k) (hkI : k ≤ I) (Q : ℝ) (hQ : 0 < Q) :
    (Q = ∑ i ∈ Finset.univ.filter (fun i : Fin I => (i : ℕ) < k), br4c γ A b w θ (c i) Q ↔
      Q * ((1 / Q ^ θ) * (3 / (A - b * w))) ^ (3 / 2 : ℝ) =
        (γ / (b * (psum c k / k))) * (2 - (2 - 3 * θ) / k)) ∧
    (Q = ∑ i ∈ Finset.univ.filter (fun i : Fin I => (i : ℕ) < k), br4c γ A b w θ (c i) Q ↔
      Q = Q5c γ A b w θ c k) := by sorry

end CoProdBundle.Equil
