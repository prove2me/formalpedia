-- Prove2me | Theorems.Thm_EqualSubsetSum_Faster_eq_41
-- name    : EqualSubsetSum.Faster.eq_41
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T23:23:48.835207+00:00
-- url     : https://prove2.me/theorems/f71545bf-79d9-42c1-b332-e608ccc439d0
-- title:
--   §7.2, eq. (41) — closing inequality .7336067 < log₂ 1.662791
-- statement:
--   With $c_\star=.7336065$,
--   $$c_\star+.0000002=.7336067<\log_2(1.662791),$$
--   and $\log_2(1.662791)\in[.733606844384456884054702,\ .733606844384456884054703]$.
--
--   It converts the procedures' exponent bound $c_\star$ plus the finite-construction allowance into the base $1.662791$ of Theorem 1.1.
--
--   Differences from the source: none.
-- source:
--   Cheshm Jahan, Keshavarz Hedayati, Safari, Shahrezaei, Faster Equal-Subset-Sum via Truncated Inclusion–Exclusion, STOC 2027 submission (manuscript, sha256 7ad8c8b2…61dacd1), p. 46, §7.2, eq. (41)

import Mathlib
import Definitions.Def_EqualSubsetSum_Faster_Exponents

namespace EqualSubsetSum.Faster

/-- §7.2, eq. (41) (p. 46). `c★ + .0000002 = .7336067 < log₂(1.662791)`, and
`log₂(1.662791) ∈ [.733606844384456884054702, .733606844384456884054703]`. -/
theorem eq_41 :
    cStar + 2 / 10 ^ 7 = 7336067 / 10 ^ 7 ∧
    (7336067 / 10 ^ 7 : ℝ) < Real.logb 2 (1662791 / 10 ^ 6) ∧
    Real.logb 2 (1662791 / 10 ^ 6) ∈
      Set.Icc (733606844384456884054702 / 10 ^ 24 : ℝ) (733606844384456884054703 / 10 ^ 24) := by sorry

end EqualSubsetSum.Faster
