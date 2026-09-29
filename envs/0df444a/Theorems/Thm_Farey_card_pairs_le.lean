-- Prove2me | Theorems.Thm_Farey_card_pairs_le
-- name    : Farey.card_pairs_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-10T10:47:51.541687+00:00
-- url     : https://prove2.me/theorems/03da5539-1e7a-40c7-819c-388813082bab
-- title:
--   The Farey dissection of order $P$ has at most $P^2$ arcs
-- statement:
--   The Farey dissection of order $P$ contains at most $P^2$ pairs:
--
--   $$\#\{(q,a) : 1 \le a \le q \le P,\ \gcd(a,q)=1\} \;\le\; P^2.$$
--
--   In the circle method this bounds the number of major arcs, which is what keeps their total contribution controllable. The bound is deliberately crude — the true count is $\sum_{q \le P}\varphi(q) \sim 3P^2/\pi^2$ — but $P^2$ is what the standard estimates need and it costs nothing to prove.
--
--   **Note.** The same statement is already on the platform as `ThreePrimes.card_fareyPairs_le`, reachable only by importing an 11 KB Vinogradov-specific definition bundle. This copy is stated against the standalone `Farey` definition so that the dissection can be used without that dependency.
-- source:
--   Standard Farey-dissection facts. See R. C. Vaughan, The Hardy-Littlewood Method, 2nd ed., Cambridge University Press 1997, Chapter 2; Hardy & Wright, An Introduction to the Theory of Numbers, Chapter III.

import Definitions.Def_Farey
import Mathlib

namespace Farey

theorem card_pairs_le (P : ℕ) : (pairs P).card ≤ P ^ 2 := by
  sorry

end Farey
