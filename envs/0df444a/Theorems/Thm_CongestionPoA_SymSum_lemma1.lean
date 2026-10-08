-- Prove2me | Theorems.Thm_CongestionPoA_SymSum_lemma1
-- name    : CongestionPoA.SymSum.lemma1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T17:31:23.272993+00:00
-- url     : https://prove2.me/theorems/2ef38d34-12df-44cb-8ace-4ba846421041
-- title:
--   Lemma 1 — $\beta(\alpha+1)\le\frac13\alpha^2+\frac53\beta^2$ for nonnegative integers
-- statement:
--   For every pair of nonnegative integers $\alpha,\beta$,
--   $$\beta(\alpha+1)\le \tfrac13\alpha^2+\tfrac53\beta^2.$$
--
--   This elementary inequality converts the cross terms $n_e(P)(n_e(A)+1)$ that arise when the Nash deviation inequalities are summed into the squares that make up $\mathrm{SUM}(A)$ and $\mathrm{SUM}(P)$.
--
--   **Formalization Note** The inequality is read in the reals for natural numbers $\alpha,\beta$; integrality matters, since it fails for $\alpha=0$, $\beta=1/2$.
-- source:
--   Christodoulou and Koutsoupias, The Price of Anarchy of Finite Congestion Games, STOC 2005, DOI 10.1145/1060590.1060600, PDF p. 3, Lemma 1

import Mathlib

namespace CongestionPoA.SymSum

/-- Christodoulou and Koutsoupias, *The Price of Anarchy of Finite Congestion Games*, STOC 2005,
PDF p. 3, Lemma 1: for every pair of nonnegative integers `α, β`,
`β(α + 1) ≤ (1/3)α² + (5/3)β²`. Used in the last step of the proof of Theorem 3 (PDF p. 4).

**Formalization Note.** `α` and `β` range over `ℕ` and the inequality is read in `ℝ`. Integrality is
essential: over the reals the inequality fails at `α = 0`, `β = 1/2`. -/
theorem lemma1 (α β : ℕ) :
    (β : ℝ) * ((α : ℝ) + 1) ≤ (1 / 3 : ℝ) * (α : ℝ) ^ 2 + (5 / 3 : ℝ) * (β : ℝ) ^ 2 := by sorry

end CongestionPoA.SymSum
