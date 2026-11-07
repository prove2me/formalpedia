-- Prove2me | Theorems.Thm_AC02Frege_eq_49_sampling_tail
-- name    : AC02Frege.eq_49_sampling_tail
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:46:32.391243+00:00
-- url     : https://prove2.me/theorems/99333530-849a-4e40-96f9-5893ac45cd5d
-- title:
--   Eq. (49) — tail bound for sampling without replacement
-- statement:
--   Choose a uniform $j$-subset of an $N$-element set, $0\le j\le N$. For a fixed set $I$ of $L\ge1$ coordinates, let $X$ count how many are selected, and put $p=j/N$. For every $u\ge0$,
--   $$
--   \Pr[X-Lp\ge u]\le\exp(-2u^2/L).
--   $$
--
--   This is the tail estimate behind the bound (33) on the fraction of monomials excluded by $W_Q$.
--
--   Differences from the source:
--   - encoding: the probability under a uniform j-subset → the number of j-subsets S of Fin N with |S ∩ I| − |I| j/N ≥ u, divided by C(N, j); reason: the uniform distribution on j-subsets
-- source:
--   Alekseev, Gryaznov, Pitassi, Robere, Shekhovtsov, Tzameret, Progress on AC0[2]-Frege Lower Bounds (manuscript dated November 3, 2026, STOC 2027 submission, sha256 88d149fa2bcae702e55a6b72efecda2b4137fd18dca3e23a056c3db5da0ece61), App. C, (49), p.45

import Mathlib

namespace AC02Frege

/-- Alekseev–Gryaznov–Pitassi–Robere–Shekhovtsov–Tzameret, *Progress on AC0[2]-Frege Lower Bounds*, manuscript (sha256 88d149fa…), App. C, (49), p.45 (tail bound for sampling without replacement): choose a uniform
`j`-subset of an `N`-element set; for a fixed set of `L ≥ 1` coordinates let `X` count how many
are selected, and put `p = j/N`. For every `u ≥ 0`, `Pr[X − Lp ≥ u] ≤ exp(−2u²/L)`.

**Formalization Note** The probability is the fraction of `j`-subsets `S` of `Fin N` with
`|S ∩ I| − |I| j/N ≥ u`, over `C(N, j)`; `0 ≤ j ≤ N`. -/
theorem eq_49_sampling_tail (N j : ℕ) (hj : j ≤ N) (I : Finset (Fin N)) (hI : 1 ≤ I.card)
    (u : ℝ) (hu : 0 ≤ u) :
    ((((Finset.univ : Finset (Finset (Fin N))).filter (fun S => S.card = j ∧
        u ≤ ((S ∩ I).card : ℝ) - (I.card : ℝ) * ((j : ℝ) / N))).card : ℕ) : ℝ)
        / (N.choose j : ℝ)
      ≤ Real.exp (-2 * u ^ 2 / I.card) := by sorry

end AC02Frege
