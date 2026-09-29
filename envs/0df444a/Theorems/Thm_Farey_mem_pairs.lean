-- Prove2me | Theorems.Thm_Farey_mem_pairs
-- name    : Farey.mem_pairs
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-10T10:47:52.48199+00:00
-- url     : https://prove2.me/theorems/711d947b-50ee-4395-ac0b-daf94d89e2ca
-- title:
--   Membership in the Farey dissection of order $P$
-- statement:
--   A pair $(q,a)$ of natural numbers belongs to the Farey dissection of order $P$ if and only if
--
--   $$1 \le q \le P, \qquad 1 \le a \le q, \qquad \gcd(a,q) = 1.$$
--
--   This unfolds the definition, which is built as an iterated union over denominators, into the flat list of conditions one actually reasons with. It is the workhorse lemma for the dissection: every other statement about Farey pairs is proved by rewriting membership this way.
-- source:
--   Standard Farey-dissection facts. See R. C. Vaughan, The Hardy-Littlewood Method, 2nd ed., Cambridge University Press 1997, Chapter 2; Hardy & Wright, An Introduction to the Theory of Numbers, Chapter III.

import Definitions.Def_Farey
import Mathlib

namespace Farey

theorem mem_pairs {P : ℕ} {p : ℕ × ℕ} :
    p ∈ pairs P ↔ 1 ≤ p.1 ∧ p.1 ≤ P ∧ 1 ≤ p.2 ∧ p.2 ≤ p.1 ∧ Nat.Coprime p.2 p.1 := by
  sorry

end Farey
