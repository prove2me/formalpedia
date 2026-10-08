-- Prove2me | Theorems.Thm_ChoiceRM_MNL_mix_ge_below_kstar
-- name    : ChoiceRM.MNL.mix_ge_below_kstar
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:51:37.339992+00:00
-- url     : https://prove2.me/theorems/d2d67085-9dfe-45e6-b221-7fb2617e86d3
-- title:
--   Proof of Proposition 6, p. 24 — for j ≤ k*, P̄_j(α) = w_j/(Σ_{i∈T} w_i + 1) ≥ P_j(T)
-- statement:
--   Let $w_1, \dots, w_n > 0$, $W(S) = \sum_{i\in S} w_i$, and let $P_j(S)$ be the MNL probabilities (14). Let $T \subseteq N$, let $0 \le k^* < n$ satisfy $W(A_{k^*}) \le W(T) < W(A_{k^*+1})$, and let $\theta \in [0,1]$ satisfy (15). With the convex weights $\alpha_{k^*} = \theta$, $\alpha_{k^*+1} = 1 - \theta$ and $\alpha_k = 0$ otherwise, and $\bar P_j(\alpha) = \sum_{k} \alpha_k P_j(A_k)$, every product $j \le k^*$ satisfies
--   $$
--   \bar P_j(\alpha) = \theta \frac{w_j}{W(A_{k^*}) + 1} + (1-\theta)\frac{w_j}{W(A_{k^*+1}) + 1} = \frac{w_j}{W(T) + 1} \ \ge\ P_j(T).
--   $$
--
--   Summed over $j \le i$, this gives the majorization inequalities of Theorem 2 (ii) for the prefixes $A_i$ with $i \le k^*$.
--
--   **Formalization Note** The paper's $\lambda$ is written $\theta$ (`λ` is reserved in Lean). Products are `Fin n`; the paper's $j \le k^*$ (1-based) is `j.val < k` (0-based). The weights are `twoPoint k θ` on the index set $\{0, \dots, n\}$.
-- source:
--   Talluri, van Ryzin, Revenue management under a general discrete choice model of consumer behavior, working paper of October 21, 2001 (UPF Economics Working Paper 533; published Management Science 50(1), 2004, DOI 10.1287/mnsc.1030.0147), p. 24, proof of Proposition 6, eq. (16) and the display for j ≤ k*

import Mathlib
import Definitions.Def_RevenueManagement_singleResource
import Definitions.Def_ChoiceRM_MNL_FareOrder
import Definitions.Def_ChoiceRM_MNL_Models

namespace ChoiceRM.MNL

/-- Proof of Proposition 6, p. 24: with `k*`, `θ` (the paper's `λ`) as in (15) and the
two-point weights `α_{k*} = θ`, `α_{k*+1} = 1 − θ`, every fare `j ≤ k*` (0-based `j < k`) has
`P̄_j(α) = w_j / (W(T) + 1) ≥ P_j(T)`. -/
theorem mix_ge_below_kstar {n : ℕ} (w : Fin n → ℝ) (hw : ∀ j, 0 < w j)
    (T : Finset (Fin n)) (k : ℕ) (hk : k < n)
    (hlo : ∑ i ∈ complete n k, w i ≤ ∑ i ∈ T, w i)
    (hhi : ∑ i ∈ T, w i < ∑ i ∈ complete n (k + 1), w i)
    (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (h15 : θ * ((∑ i ∈ complete n k, w i) / (∑ i ∈ complete n k, w i + 1)) +
        (1 - θ) * ((∑ i ∈ complete n (k + 1), w i) /
          (∑ i ∈ complete n (k + 1), w i + 1)) =
      (∑ i ∈ T, w i) / (∑ i ∈ T, w i + 1)) :
    ∀ j : Fin n, j.val < k →
      mixProb (mnl w) (twoPoint k θ) j = w j / (∑ i ∈ T, w i + 1) ∧
        mnl w T j ≤ w j / (∑ i ∈ T, w i + 1) := by sorry

end ChoiceRM.MNL
