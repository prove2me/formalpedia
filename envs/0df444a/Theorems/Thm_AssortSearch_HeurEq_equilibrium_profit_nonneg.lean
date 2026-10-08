-- Prove2me | Theorems.Thm_AssortSearch_HeurEq_equilibrium_profit_nonneg
-- name    : AssortSearch.HeurEq.equilibrium_profit_nonneg
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:32:50.083439+00:00
-- url     : https://prove2.me/theorems/d0db3d66-7284-4269-8526-6b36f97e6749
-- title:
--   A heuristic equilibrium carries no variant with negative expected profit: $\pi_i(x^*)\ge 0$
-- statement:
--   Consider the independent assortment search model with $v_1\ge\dots\ge v_n>0$, $v_0>0$, $\lambda>0$, monotone margins ($m_j\ge m_k$ whenever $v_j\ge v_k$) and an operational cost $c$ that is concave and increasing on $[0,1]$ with $c(0)\ge 0$. Let $x^*$ be a heuristic equilibrium of iterative no-search assortment planning. Then every variant of $x^*$ has non-negative expected profit:
--   $$\pi_i(x^*)=m_i\,q_i^m(x^*\mid\hat v(x^*))-c\big(q_i^m(x^*\mid\hat v(x^*))\big)\ \ge\ 0\qquad(1\le i\le x^*).$$
--
--   Here the demand $q_i^m(x^*\mid\hat v(x^*))$ is the no-search prediction with the estimated preferences, which coincides with the observed demand $d_i(x^*)$. The paper asserts this step in the proof of Theorem 8 ("as we show in the previous section"), referring to its remark in §4.3 that an optimal assortment contains no non-positive-profit variant because of cannibalization.
--
--   **Formalization Note** $c(0)\ge 0$ is an added hypothesis: the paper never states $c(0)$, and the step can fail without it. Monotone preferences and margins are the paper's standing assumptions (§3, pp. 5–6). The §4.3 remark says "strictly positive", which is false for a zero-profit variant; the non-strict form of p. 23 is stated.
-- source:
--   Cachon, Terwiesch & Xu, Retail Assortment Planning in the Presence of Consumer Search, working paper (Dec. 20, 2002), p. 23 (PDF 25), proof of Theorem 8, π_i(x*) ≥ 0; cf. p. 17 (PDF 19), §4.3

import Mathlib
import Definitions.Def_AssortSearch_HeurEq_Model

namespace AssortSearch.HeurEq

open RetailVariety.Structure

/-- Proof of Theorem 8, p. 23 (asserted there "as we show in the previous section"): a
heuristic equilibrium `x*` contains no variant with negative expected profit (as estimated under
`v̂(x*)`, which reproduces the observed demands at `x*`):
`π_i(x*) = m_i q_i^m(x* | v̂(x*)) − c(q_i^m(x* | v̂(x*))) ≥ 0` for all `1 ≤ i ≤ x*`. -/
theorem equilibrium_profit_nonneg {n : ℕ} (lam : ℝ) (m : Fin n → ℝ) (c : ℝ → ℝ)
    (v : Fin n → ℝ) (v0 : ℝ)
    (hv : ∀ i, 0 < v i) (hanti : Antitone v) (hv0 : 0 < v0) (hlam : 0 < lam)
    (hm : ∀ j k : Fin n, v k ≤ v j → m k ≤ m j)
    (hcc : ConcaveOn ℝ (Set.Icc 0 1) c) (hcm : MonotoneOn c (Set.Icc 0 1))
    (hc0 : 0 ≤ c 0)
    (xstar : ℕ) (heq : IsHeuristicEquilibrium lam m c v v0 xstar)
    (i : Fin n) (hi : i.val < xstar) :
    0 ≤ m i * share (estPref lam v v0 xstar) (estPrefNoPurchase lam v v0 xstar)
          (popularSet n xstar) i -
        c (share (estPref lam v v0 xstar) (estPrefNoPurchase lam v v0 xstar)
          (popularSet n xstar) i) := by sorry

end AssortSearch.HeurEq
