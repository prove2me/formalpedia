-- Prove2me | Theorems.Thm_BayesBAI_proposition_9
-- name    : BayesBAI.proposition_9
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:52:55.572507+00:00
-- url     : https://prove2.me/theorems/7b97f934-7336-4681-9816-c984aa974afd
-- title:
--   Proposition 9 — Stirling's approximation, two-sided
-- statement:
--   For every integer $n\ge1$,
--   $$
--   \sqrt{2\pi}\,n^{n+\frac12}e^{-n}e^{\frac1{12n+1}}<n!<\sqrt{2\pi}\,n^{n+\frac12}e^{-n}e^{\frac1{12n}},
--   $$
--   and
--   $$
--   \sqrt{2\pi}\,n^{n+\frac12}e^{-n}<n!<\sqrt{2\pi}\,n^{n+\frac12}e^{-n}\Big(1+\frac1{6n}\Big).
--   $$
--   These are the bounds behind the leading constant in Lemma 15.
--
--   Differences from the source:
--   - encoding: n ∈ ℕ; the second pair "by using e^(1/n) ≤ 1 + 2/n for n ≥ 2" → 1 ≤ n, all four inequalities; reason: 1/(12n) is undefined at n = 0, and the second pair uses that bound at 12n ≥ 2
-- source:
--   Komiyama, Ariu, Kato, Qin, Rate-optimal Bayesian Simple Regret in Best Arm Identification, arXiv:2111.09885v3, Proposition 9, p.17

import Mathlib

namespace BayesBAI

/-- Proposition 9 (Stirling's approximation), Komiyama, Ariu, Kato, Qin, arXiv:2111.09885v3, p.17:
for `n ≥ 1`, `√(2π) n^(n+1/2) e^(-n) e^(1/(12n+1)) < n! < √(2π) n^(n+1/2) e^(-n) e^(1/(12n))` and
`√(2π) n^(n+1/2) e^(-n) < n! < √(2π) n^(n+1/2) e^(-n) (1 + 1/(6n))`.

**Formalization Note.** "`n ∈ ℕ`" means `n ≥ 1`, as `1/(12n)` is undefined at `0`. -/
theorem proposition_9 (n : ℕ) (hn : 1 ≤ n) :
    Real.sqrt (2 * Real.pi) * (n : ℝ) ^ ((n : ℝ) + 1 / 2) * Real.exp (-(n : ℝ)) *
        Real.exp (1 / (12 * (n : ℝ) + 1)) < (n.factorial : ℝ) ∧
    (n.factorial : ℝ) < Real.sqrt (2 * Real.pi) * (n : ℝ) ^ ((n : ℝ) + 1 / 2) * Real.exp (-(n : ℝ)) *
        Real.exp (1 / (12 * (n : ℝ))) ∧
    Real.sqrt (2 * Real.pi) * (n : ℝ) ^ ((n : ℝ) + 1 / 2) * Real.exp (-(n : ℝ)) <
        (n.factorial : ℝ) ∧
    (n.factorial : ℝ) < Real.sqrt (2 * Real.pi) * (n : ℝ) ^ ((n : ℝ) + 1 / 2) * Real.exp (-(n : ℝ)) *
        (1 + 1 / (6 * (n : ℝ))) := by sorry

end BayesBAI
