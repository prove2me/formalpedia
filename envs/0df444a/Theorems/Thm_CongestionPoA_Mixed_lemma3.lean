-- Prove2me | Theorems.Thm_CongestionPoA_Mixed_lemma3
-- name    : CongestionPoA.Mixed.lemma3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T17:50:18.830235+00:00
-- url     : https://prove2.me/theorems/6d6f04d8-8880-4b21-97ce-02e72a20ed26
-- title:
--   Lemma 3 (corrected) — y(x+1) ≤ ((√5−1)/4)x² + ((√5+5)/4)y² for real x ≥ 0 and integer y ≥ 0
-- statement:
--   For every nonnegative real number $x$ and every nonnegative integer $y$,
--   $$y(x+1) \le \frac{\sqrt5 - 1}{4}\,x^2 + \frac{\sqrt5 + 5}{4}\,y^2.$$
--
--   This is the real relaxation of Lemma 1 that the paper uses for mixed equilibria (Sect. 5): applied with $x$ the expected load of a facility under a mixed Nash equilibrium and $y$ its load in a comparison profile, it turns the summed deviation inequality into a bound on the mixed social cost with constant $(3+\sqrt5)/2$.
--
--   **Formalization Note** The paper states the lemma "for every non negative reals $x, y$". As printed it is false: at $x = 0$, $y = 1/10$ the left side is $0.1$ and the right side $(\sqrt5+5)/400 \approx 0.018$. The statement here keeps $y$ an integer, which is how the lemma is used (a facility load) and under which it holds.
-- source:
--   Christodoulou and Koutsoupias, The Price of Anarchy of Finite Congestion Games, STOC 2005, DOI 10.1145/1060590.1060600, PDF p. 6, Lemma 3 (corrected: y a nonnegative integer)

import Mathlib

namespace CongestionPoA.Mixed

/-- Christodoulou and Koutsoupias, *The Price of Anarchy of Finite Congestion Games*, STOC 2005,
PDF p. 6, Lemma 3 (corrected): for every nonnegative real `x` and every nonnegative integer `y`,
`y(x + 1) ≤ ((√5 − 1)/4)·x² + ((√5 + 5)/4)·y²`.

**Formalization Note.** The paper prints "For every non negative reals x, y". With `y` real the
inequality is false (`x = 0`, `y = 1/10`: the left side is `0.1`, the right side `(√5+5)/400 ≈ 0.018`).
The lemma relaxes Lemma 1 "to deal with reals instead of integers", and in the proof of Theorem 14 it
is applied with `x` the expected load of a facility (a real number) and `y` its load in the comparison
profile (an integer); so `x` is real and `y` stays a natural number. -/
theorem lemma3 (x : ℝ) (hx : 0 ≤ x) (y : ℕ) :
    (y : ℝ) * (x + 1) ≤ (Real.sqrt 5 - 1) / 4 * x ^ 2 + (Real.sqrt 5 + 5) / 4 * (y : ℝ) ^ 2 := by sorry

end CongestionPoA.Mixed
