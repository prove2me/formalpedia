-- Prove2me | Theorems.Thm_ExplodingOffer_Mrl_eq_5_6
-- name    : ExplodingOffer.Mrl.eq_5_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:18:38.231013+00:00
-- url     : https://prove2.me/theorems/67e982d0-0023-4888-af3b-13918edb6f8d
-- title:
--   §4, eqs. (5)–(6), p. 9 — P(N(0,t_D) = 0) = ℒ(V(0; s, t_D))/ℒ(s), so Π(s,t_D) = (u − s)ℒ(V(0; s, t_D))/ℒ(s)
-- statement:
--   Let $X$ be a nonnegative continuous random variable with support $[a,b]$ and finite mean, $\lambda > 0$, $T > 0$, and let $(s, t_D)$ satisfy $0 \le t_D \le T$, $v(t_D) \le s < b$. Then the probability that the responder accepts none of the alternative offers during $[0, t_D]$ is
--   $$\mathbb P(N(0,t_D) = 0) = \exp\Big[-\lambda \int_0^{t_D} \mathbb P(X \ge V(t; s, t_D))\,dt\Big] = \frac{\mathcal L(V(0; s, t_D))}{\mathcal L(s)},$$
--   and therefore, for every $u$, the proposer's surplus is
--   $$\Pi(s,t_D) = (u - s)\,\frac{\mathcal L(V(0; s, t_D))}{\mathcal L(s)}.$$
--
--   This closed form of the surplus is the starting point of the proposer's optimization.
--
--   **Formalization Note** $\Pi$ is defined from the no-acceptance probability (the first equality of (6)), so the ratio form is a theorem, not a definition. The restriction $s < b$ is where $\mathcal L(s) > 0$; for $s \ge b$ the page's ratio is $0/0$.
-- source:
--   Hu & Tang, Size Matters, So Does Duration: The Interplay between Offer Size and Offer Deadline, SSRN preprint 3143414 (version of 2020-05-16), p. 9, §4, eqs. (5)–(6)

import Mathlib
import Definitions.Def_ExplodingOffer_Mrl_Model

namespace ExplodingOffer.Mrl

open MeasureTheory

theorem eq_5_6 {μ : Measure ℝ} {a : ℝ} {b : EReal} (hμ : OfferDist μ a b)
    {lam T : ℝ} (hlam : 0 < lam) (hT : 0 < T)
    {s tD : ℝ} (htD0 : 0 ≤ tD) (htDT : tD ≤ T) (hs : minAccept μ b lam T tD ≤ s)
    (hsb : (s : EReal) < b) (u : ℝ) :
    noAcceptProb μ b lam T s tD = Lfun μ (valueToGo μ b lam T s tD 0) / Lfun μ s ∧
    surplus μ b lam T u s tD =
      (u - s) * (Lfun μ (valueToGo μ b lam T s tD 0) / Lfun μ s) := by sorry

end ExplodingOffer.Mrl
