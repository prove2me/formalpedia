-- Prove2me | Theorems.Thm_CongestionPoA_SymMax_lemma1
-- name    : CongestionPoA.SymMax.lemma1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T08:46:26.952645+00:00
-- url     : https://prove2.me/theorems/06764d57-2fea-4961-8be0-de6f11e3aec4
-- title:
--   Lemma 1 — $\beta(\alpha+1)\le\frac13\alpha^2+\frac53\beta^2$ for nonnegative integers
-- statement:
--   For every pair of nonnegative integers $\alpha,\beta$,
--   $$\beta(\alpha+1)\;\le\;\tfrac13\alpha^2+\tfrac53\beta^2 .$$
--
--   This elementary inequality is the arithmetic core of the $5/2$ bounds of the paper; the proof of Theorem 7 uses it with $\alpha=n_e(A)$ and $\beta=n_e(P)$.
--
--   **Formalization Note** $\alpha,\beta$ are natural numbers and the inequality is read in the reals. Integrality matters: the inequality fails for $\alpha=0$, $\beta=1/2$. The same lemma is drafted in mission I of this series; the two copies are the same statement.
-- source:
--   Christodoulou and Koutsoupias, The Price of Anarchy of Finite Congestion Games, STOC 2005, DOI 10.1145/1060590.1060600, PDF p. 3, Lemma 1

import Mathlib

namespace CongestionPoA.SymMax

/-- Christodoulou and Koutsoupias, *The Price of Anarchy of Finite Congestion Games*, STOC 2005,
PDF p. 3, Lemma 1: for every pair of nonnegative integers `α, β`,
`β(α + 1) ≤ (1/3)α² + (5/3)β²`. Used in the proof of Theorem 7 (PDF p. 5).

**Formalization Note.** `α` and `β` range over `ℕ` and the inequality is read in `ℝ`. Integrality is
essential: over the reals the inequality fails at `α = 0`, `β = 1/2`. -/
theorem lemma1 (α β : ℕ) :
    (β : ℝ) * ((α : ℝ) + 1) ≤ (1 / 3 : ℝ) * (α : ℝ) ^ 2 + (5 / 3 : ℝ) * (β : ℝ) ^ 2 := by sorry

end CongestionPoA.SymMax
