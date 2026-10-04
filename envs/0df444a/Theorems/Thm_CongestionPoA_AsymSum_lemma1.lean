-- Prove2me | Theorems.Thm_CongestionPoA_AsymSum_lemma1
-- name    : CongestionPoA.AsymSum.lemma1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T08:28:16.444917+00:00
-- url     : https://prove2.me/theorems/90a48d13-74bf-414b-965b-32d1ac73a978
-- title:
--   Lemma 1 — $\beta(\alpha+1) \le \frac13\alpha^2 + \frac53\beta^2$ for nonnegative integers
-- statement:
--   For every pair of nonnegative integers $\alpha,\beta$,
--   $$\beta(\alpha+1)\le \frac13\alpha^2+\frac53\beta^2.$$
--
--   This elementary inequality is the arithmetic heart of the $5/2$ bound for the average social cost: applied facility by facility with $\alpha=n_e(A)$ and $\beta=n_e(P)$, it turns the bound obtained from the Nash conditions into a bound by $\frac13\mathrm{SUM}(A)+\frac53\mathrm{SUM}(P)$.
--
--   **Formalization Note** $\alpha$ and $\beta$ are natural numbers and the inequality is read in the reals. The hypothesis that they are integers is essential: for real $\alpha=0$, $\beta=1/2$ the left side is $1/2$ and the right side is $5/12$.
-- source:
--   Christodoulou and Koutsoupias, The Price of Anarchy of Finite Congestion Games, STOC 2005, DOI 10.1145/1060590.1060600, PDF p. 3, Lemma 1

import Mathlib

namespace CongestionPoA.AsymSum

/-- Christodoulou and Koutsoupias, *The Price of Anarchy of Finite Congestion Games*, STOC 2005,
PDF p. 3, Lemma 1: for every pair of nonnegative integers `α, β`,
`β(α + 1) ≤ (1/3)α² + (5/3)β²`.

**Formalization Note.** `α` and `β` range over `ℕ` and the inequality is read in `ℝ`. Integrality is
essential: over the reals the inequality fails at `α = 0`, `β = 1/2`. -/
theorem lemma1 (α β : ℕ) :
    (β : ℝ) * ((α : ℝ) + 1) ≤ (1 / 3 : ℝ) * (α : ℝ) ^ 2 + (5 / 3 : ℝ) * (β : ℝ) ^ 2 := by sorry

end CongestionPoA.AsymSum
