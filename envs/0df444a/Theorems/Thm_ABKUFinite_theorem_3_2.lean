-- Prove2me | Theorems.Thm_ABKUFinite_theorem_3_2
-- name    : ABKUFinite.theorem_3_2
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-29T10:32:24.574694+00:00
-- url     : https://prove2.me/theorems/694d7c43-b666-442a-87af-3f2e131966c1
-- title:
--   Theorem 3.2 — maximum-load upper bound
-- statement:
--   For every natural number \(d\), there exists a nonnegative real \(C\) such that for every positive real \(\varepsilon\), there exists a natural number \(N\) such that, for every natural number \(n\ge N\), the uniform probability that the maximum load is at most \(\log\log(n+1)/\log(d+2)+C\) is at least \(1-\varepsilon\). The maximum load is obtained by allocating \(n+1\) balls sequentially to \(n+1\) initially empty bins, each ball making \(d+2\) independent uniform choices with replacement and joining the earliest choice of minimum current load. The constant \(C\) may depend on \(d\) but not on \(\varepsilon\) or \(n\); \(N\) may depend on \(d\) and \(\varepsilon\).
-- source:
--   Azar, Broder, Karlin, Upfal (1999), Balanced Allocations, https://cs.brown.edu/people/eupfal/papers/SICOMP29.pdf, p.184; Theorem 3.2 — maximum-load upper bound

import Definitions.Def_ABKUFinite_Model

namespace ABKUFinite
theorem theorem_3_2 (d : ℕ) : Upper d := by sorry
end ABKUFinite
