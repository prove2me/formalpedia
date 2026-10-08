-- Prove2me | Theorems.Thm_FedergruenZipkin_AvgCost_corollary1_hitting_sums
-- name    : FedergruenZipkin.AvgCost.corollary1_hitting_sums
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T14:38:10.748595+00:00
-- url     : https://prove2.me/theorems/af9b0d61-e345-4f01-b85d-ed2786f846de
-- title:
--   Corollary 1 (p. 200) — $H_\iota v1 = O(|x|^3)$ and $H_\iota G = O(|x|^{\rho+3})$, both finite
-- statement:
--   In the capacitated inventory model with storage capacity $U$, let $\iota = [l, u]$ with $0 \le u \le U$ and $l \le u - b$, and let $H_\iota$ be the hitting-sum operator of Lemma 3. Let $v1$ be the constant function $1$ and $G$ the one-period cost, which satisfies $G(y) \le A + B|y|^\rho$ (Assumption 3). Then there are constants such that for all $x \le U$
--   $$H_\iota v1(x) \le A_1 + B_1 |x|^3,\qquad H_\iota G(x) \le A_2 + B_2 |x|^{\rho+3}.$$
--   In particular both functions are finite-valued on $x \le U$.
--
--   $H_\iota v1(x)$ is the largest expected time, over policies in $\Delta_\iota$, for the inventory starting at $x$ to enter $\iota$, and $H_\iota G(x)$ is the largest expected cost incurred meanwhile. Their finiteness is condition FST2(a) in the paper's proof of Theorem 1.
--
--   **Formalization Note** $H_\iota$ is $[0,\infty]$-valued, so the growth bounds already imply finiteness; the finiteness clause is kept because the corollary states it.
-- source:
--   Federgruen and Zipkin, An Inventory Model with Limited Production Capacity and Uncertain Demands I, Math. Oper. Res. 11(2), 1986, p. 200, Corollary 1

import Mathlib
import Definitions.Def_FedergruenZipkin_AvgCost_Model

namespace FedergruenZipkin.AvgCost
open scoped ENNReal
theorem corollary1_hitting_sums (M : Model) (U l u : ℤ) (hu0 : 0 ≤ u) (huU : u ≤ U)
    (hlu : l ≤ u - M.b) :
    (∃ A B : ℝ, ∀ x ≤ U,
      H M U l u (fun _ => (1 : ℝ≥0∞)) x ≤ ENNReal.ofReal (A + B * |(x : ℝ)| ^ 3)) ∧
    (∃ A B : ℝ, ∀ x ≤ U,
      H M U l u (fun y => ENNReal.ofReal (M.G y)) x ≤
        ENNReal.ofReal (A + B * |(x : ℝ)| ^ (M.ρ + 3))) ∧
    ∀ x ≤ U, H M U l u (fun _ => (1 : ℝ≥0∞)) x ≠ ⊤ ∧
      H M U l u (fun y => ENNReal.ofReal (M.G y)) x ≠ ⊤ := by sorry
end FedergruenZipkin.AvgCost
