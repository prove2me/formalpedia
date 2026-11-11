-- Prove2me | Theorems.Thm_EqualSubsetSum_Faster_eq_3
-- name    : EqualSubsetSum.Faster.eq_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T23:26:39.635864+00:00
-- url     : https://prove2.me/theorems/d5fe62e6-f030-417a-a16b-2f9d49b8ac76
-- title:
--   §4.1, eq. (3) — truncated inclusion–exclusion identity
-- statement:
--   For integers $c\ge1$ and $d\ge0$, Pascal's rule makes the partial sums telescope:
--   $$\sum_{q=0}^{d}(-1)^q\binom cq=(-1)^d\binom{c-1}{d}.$$
--   Hence, for even $d$,
--   $$f_d(c):=\sum_{q=0}^{d}(-1)^q\binom cq=\begin{cases}1,&c=0,\\0,&1\le c\le d,\\ \binom{c-1}{d},&c>d.\end{cases}$$
--   It is the identity behind the upper partner counts $U(a)$ of the detector.
--
--   Differences from the source: none.
-- source:
--   Cheshm Jahan, Keshavarz Hedayati, Safari, Shahrezaei, Faster Equal-Subset-Sum via Truncated Inclusion–Exclusion, STOC 2027 submission (manuscript, sha256 7ad8c8b2…61dacd1), p. 22, §4.1, eq. (3)

import Mathlib
import Definitions.Def_EqualSubsetSum_Faster_Detector

namespace EqualSubsetSum.Faster

/-- §4.1, eq. (3) (p. 22). For `c ≥ 1` the partial sums `∑_{q=0}^{d} (-1)^q (c choose q)`
telescope to `(-1)^d (c-1 choose d)`; hence for even `d`, `f_d(c)` is `1` if `c = 0`, `0` if
`1 ≤ c ≤ d`, and `(c-1 choose d)` if `c > d`. -/
theorem eq_3 :
    (∀ d c : ℕ, 1 ≤ c → truncAlt d c = (-1) ^ d * ((c - 1).choose d : ℤ)) ∧
    (∀ d c : ℕ, Even d →
        truncAlt d c = if c = 0 then 1 else if c ≤ d then 0 else ((c - 1).choose d : ℤ)) := by sorry

end EqualSubsetSum.Faster
