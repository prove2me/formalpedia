-- Prove2me | Theorems.Thm_BuyXFree_Threshold_case_c_stationary
-- name    : BuyXFree.Threshold.case_c_stationary
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T05:11:45.057+00:00
-- url     : https://prove2.me/theorems/f60bb5df-f80e-4a29-9f37-7a34adf783da
-- title:
--   Proof of Lemma 3, pp. 45–46 — case (c) stationary probabilities and demand λqX/(X + q)
-- statement:
--   Throughout, the standing assumptions of §3 hold: $0\le\lambda\le1$, $0\le q\le1$, $0<\delta<1$, $v\ge\bar v\ge0$, $k\ge0$, and the program has a threshold $X\ge1$. Suppose the consumer's decisions follow case (c): at outside option $0$ she buys in every state $x<X$, at outside option $\bar v$ she never buys, and she redeems in state $X$ under either outside option. Then
--   $$q_i=\frac{1}{X+q}\ (i=0,\dots,X-1),\qquad q_X=\frac{q}{X+q}$$
--   is a stationary distribution of the induced chain, the only one when $\lambda>0$ and $q>0$, and the purchase probability under it is
--   $$\lambda q\sum_{i=0}^{X-1}q_i=\frac{\lambda qX}{X+q}.$$
--
--   This gives the firm's demand in case (c), the objective of the problem bounded in Lemma 3.
--
--   **Formalization Note** As for Lemma 1, uniqueness is asserted under $\lambda>0$, $q>0$.
-- source:
--   Liu, Sun & Zhang, An Analysis of "Buy X, Get One Free" Reward Programs, accepted manuscript (Operations Research 69(6), 2021; version of March 26, 2021), pp. 45–46, proof of Lemma 3 (Figure 7 and the balance equations)

import Mathlib
import Definitions.Def_BuyXFree_Threshold_Model
import Definitions.Def_MarkovChain

namespace BuyXFree.Threshold

open Matrix

/-- Proof of Lemma 3, pp. 45–46: under the case (c) behaviour, `q_i = 1/(X + q)` (`i < X`),
`q_X = q/(X + q)` is a stationary distribution of the induced chain, it is the only one when
`λ, q > 0`, and the purchase probability under it is `λqX/(X + q)`. -/
theorem case_c_stationary (P : Params) (hP : P.Standing) (p : ℝ) (X : ℕ) (hX : 1 ≤ X)
    (J : ℕ → ℝ) (hC : CaseC P p X J) :
    MarkovChain.IsStationary (trans P p X J)
        (fun i => (if i.val < X then 1 else P.q) / ((X : ℝ) + P.q)) ∧
      (0 < P.lam → 0 < P.q → ∀ μ : Fin (X + 1) → ℝ, MarkovChain.IsStationary (trans P p X J) μ →
        μ = fun i => (if i.val < X then 1 else P.q) / ((X : ℝ) + P.q)) ∧
      (fun i : Fin (X + 1) => (if i.val < X then 1 else P.q) / ((X : ℝ) + P.q)) ⬝ᵥ
          buyProb P p X J =
        P.lam * P.q * X / ((X : ℝ) + P.q) := by sorry
end BuyXFree.Threshold
