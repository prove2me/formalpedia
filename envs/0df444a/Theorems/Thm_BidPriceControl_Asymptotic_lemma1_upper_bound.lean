-- Prove2me | Theorems.Thm_BidPriceControl_Asymptotic_lemma1_upper_bound
-- name    : BidPriceControl.Asymptotic.lemma1_upper_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T11:38:38.604989+00:00
-- url     : https://prove2.me/theorems/4213620c-b14d-4a4e-9858-444befa17781
-- title:
--   Lemma 1: for any μ ≥ 0, J_k(x) ≤ J̄_k(x, μ)
-- statement:
--   Under the standing assumptions of §1 on the request laws $F_1, \dots, F_k$, for every bid-price vector $\mu \ge 0$ the optimal expected revenue of the Bellman equations (2)–(3) is bounded by the relaxed value (8):
--   $$J_k(x) \le \bar J_k(x, \mu) = \sum_{t=1}^k\sum_{j=1}^n \mathbb{E}\,(R_t^j - \mu A^j)^+ + \mu x.$$
--   Minimizing the right side over $\mu \ge 0$ gives the upper bound $v_k(x)$ of (9), the benchmark against which the heuristic is measured.
--
--   **Formalization Note.** The paper defines $\bar J_k(x, \mu)$ as the value (7) of a relaxed control problem and evaluates it as (8). This item takes (8) as the definition, so it is Lemma 1 combined with the evaluation (8).
-- source:
--   Talluri, van Ryzin, An Analysis of Bid-Price Controls for Network Revenue Management, Management Sci. 44(11), 1998, p. 1583, Lemma 1 (with the evaluation (8))

import Mathlib
import Definitions.Def_BidPriceControl_Asymptotic_Model

namespace BidPriceControl.Asymptotic

open MeasureTheory ProbabilityTheory

/-- Lemma 1 (p. 1583), with the relaxed value in its evaluated form (8): under the standing
assumptions of §1, for any `μ ≥ 0`, `J_k(x) ≤ J̄_k(x, μ)`, where `J` is the optimal expected revenue
of the Bellman equations (2)–(3). -/
theorem lemma1_upper_bound {m n : ℕ} (A : Fin m → Fin n → ℕ) (F : ℕ → Measure (Fin n → ℝ))
    (k : ℕ) (x : Fin m → ℕ) (hF : ∀ t ∈ Finset.Icc 1 k, IsRequestLaw (F t))
    (μ : Fin m → ℝ) (hμ : 0 ≤ μ) :
    optValue A F k x ≤ relaxedValue A F k x μ := by sorry

end BidPriceControl.Asymptotic
