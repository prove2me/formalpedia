-- Prove2me | Theorems.Thm_ChoiceRM_MNL_mix_partial_sums_above_kstar
-- name    : ChoiceRM.MNL.mix_partial_sums_above_kstar
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:52:02.670611+00:00
-- url     : https://prove2.me/theorems/fb8a0de8-20f1-4f44-a3ab-81161c0608b9
-- title:
--   Proof of Proposition 6, p. 25 — for j > k*, Σ_{i≤j} P̄_i(α) = W(T)/(W(T)+1) ≥ Σ_{i≤j} P_i(T)
-- statement:
--   In the setting of the previous item ($w > 0$, $W(S) = \sum_{i\in S} w_i$, $T \subseteq N$, $0 \le k^* < n$ with $W(A_{k^*}) \le W(T) < W(A_{k^*+1})$, $\theta \in [0,1]$ solving (15), and the two-point weights $\alpha_{k^*} = \theta$, $\alpha_{k^*+1} = 1-\theta$), for every prefix length $j$ with $k^* < j \le n$,
--   $$
--   \sum_{i=1}^{j} \bar P_i(\alpha) = \theta \sum_{i=1}^{k^*} \frac{w_i}{W(A_{k^*}) + 1} + (1-\theta) \sum_{i=1}^{k^*+1}\frac{w_i}{W(A_{k^*+1})+1} = \frac{W(T)}{W(T)+1} \ \ge\ \sum_{i=1}^{j} P_i(T),
--   $$
--   and the total purchase probability of $T$ is $\sum_{i=1}^n P_i(T) = W(T)/(W(T)+1)$. In particular, at $j = n$, $\sum_{i=1}^n \bar P_i(\alpha) = \sum_{i=1}^n P_i(T)$.
--
--   Together with the previous item this verifies condition (ii) of Theorem 2 for the MNL model.
--
--   **Formalization Note** The paper's $\lambda$ is written $\theta$ (`λ` is reserved in Lean). The prefix $\{1, \dots, j\}$ is `complete n i` with `k < i ≤ n` (0-based products `Fin n`).
-- source:
--   Talluri, van Ryzin, Revenue management under a general discrete choice model of consumer behavior, working paper of October 21, 2001 (UPF Economics Working Paper 533; published Management Science 50(1), 2004, DOI 10.1287/mnsc.1030.0147), p. 25, proof of Proposition 6, the display for j > k* and the case j = n

import Mathlib
import Definitions.Def_RevenueManagement_singleResource
import Definitions.Def_ChoiceRM_MNL_FareOrder
import Definitions.Def_ChoiceRM_MNL_Models

namespace ChoiceRM.MNL

/-- Proof of Proposition 6, p. 25: with `k*`, `θ` (the paper's `λ`) as in (15) and the
two-point weights, every prefix `A_i` with `i > k*` has `Σ_{j∈A_i} P̄_j(α) = W(T)/(W(T)+1) ≥
Σ_{j∈A_i} P_j(T)`, and the total `Σ_j P_j(T)` equals `W(T)/(W(T)+1)`. -/
theorem mix_partial_sums_above_kstar {n : ℕ} (w : Fin n → ℝ) (hw : ∀ j, 0 < w j)
    (T : Finset (Fin n)) (k : ℕ) (hk : k < n)
    (hlo : ∑ i ∈ complete n k, w i ≤ ∑ i ∈ T, w i)
    (hhi : ∑ i ∈ T, w i < ∑ i ∈ complete n (k + 1), w i)
    (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (h15 : θ * ((∑ i ∈ complete n k, w i) / (∑ i ∈ complete n k, w i + 1)) +
        (1 - θ) * ((∑ i ∈ complete n (k + 1), w i) /
          (∑ i ∈ complete n (k + 1), w i + 1)) =
      (∑ i ∈ T, w i) / (∑ i ∈ T, w i + 1)) :
    (∀ i : ℕ, k < i → i ≤ n →
      ∑ j ∈ complete n i, mixProb (mnl w) (twoPoint k θ) j =
          (∑ l ∈ T, w l) / (∑ l ∈ T, w l + 1) ∧
        ∑ j ∈ complete n i, mnl w T j ≤ (∑ l ∈ T, w l) / (∑ l ∈ T, w l + 1)) ∧
      ∑ j, mnl w T j = (∑ l ∈ T, w l) / (∑ l ∈ T, w l + 1) := by sorry

end ChoiceRM.MNL
