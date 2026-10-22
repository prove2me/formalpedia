-- Prove2me | Theorems.Thm_BidPriceControl_NonOptimal_eq5_value_recursion
-- name    : BidPriceControl.NonOptimal.eq5_value_recursion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T12:15:17.99535+00:00
-- url     : https://prove2.me/theorems/8ebc3cc1-3f53-403a-867e-c289b818268a
-- title:
--   Eq. (5) — J_k(x) = J_{k−1}(x) + Σ_{j : A^j ≤ x} E(R_k^j + J_{k−1}(x − A^j) − J_{k−1}(x))⁺
-- statement:
--   Let $A$ be the seat matrix of a network with $m$ legs and $n$ itineraries, and let the request vectors $R_1, \dots, R_k$ have laws $F_1, \dots, F_k$ that are probability measures concentrated on $\mathcal{S}$ (nonnegative components, at most one positive) with finite first moments. Let $J$ be the optimal expected revenue of the Bellman equations (2)–(3). Then for $k \ge 1$ and every capacity vector $x \in \mathbb{N}^m$,
--   $$J_k(x) = J_{k-1}(x) + \sum_{j : A^j \le x} \mathbb{E}\big(R_k^j + J_{k-1}(x - A^j) - J_{k-1}(x)\big)^+ .$$
--
--   This is the evaluation of the Bellman equation under the optimal control (4) at the end of the proof of Proposition 1; it expresses $J_k$ through $J_{k-1}$ and one-dimensional partial expectations, and is the formula by which a small instance is evaluated by hand.
--
--   **Formalization Note.** $J$ is `optValue`, $(\cdot)^+$ is `max · 0`, and the expectation is the Bochner integral against $F_k$. The hypothesis $k \ge 1$ guards the natural-number subtraction $k - 1$. The laws are assumed to be request laws only for the periods $1, \dots, k$ that enter $J_k$; no continuity of the fare distributions is assumed.
-- source:
--   Talluri, van Ryzin, An Analysis of Bid-Price Controls for Network Revenue Management, Management Sci. 44(11), 1998, p. 1581, eq. (5), end of the proof of Proposition 1

import Mathlib
import Definitions.Def_BidPriceControl_NonOptimal_Model

namespace BidPriceControl.NonOptimal

open MeasureTheory

/-- Equation (5) (p. 1581, end of the proof of Proposition 1): if the requests `R_1, …, R_k` have
laws on `𝒮` with finite first moments, then for `k ≥ 1` and every capacity `y`,
`J_k(y) = J_{k-1}(y) + ∑_{j : A^j ≤ y} E(R_k^j + J_{k-1}(y − A^j) − J_{k-1}(y))⁺`. -/
theorem eq5_value_recursion {m n : ℕ} (A : Fin m → Fin n → ℕ) (F : ℕ → Measure (Fin n → ℝ))
    (k : ℕ) (hk : 1 ≤ k) (hF : ∀ t ∈ Finset.Icc 1 k, IsRequestLaw (F t)) (y : Fin m → ℕ) :
    optValue A F k y = optValue A F (k - 1) y +
      ∑ j ∈ Finset.univ.filter (fun j => Fits A y j),
        ∫ r, max (r j + optValue A F (k - 1) (y - column A j) - optValue A F (k - 1) y) 0
          ∂(F k) := by sorry

end BidPriceControl.NonOptimal
