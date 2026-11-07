-- Prove2me | Theorems.Thm_FanInSemigroup_ppow_stabilizes
-- name    : FanInSemigroup.ppow_stabilizes
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:32:15.452841+00:00
-- url     : https://prove2.me/theorems/cc91a0c0-fc5a-4c05-94ce-016291705104
-- title:
--   Claim in the proof of Lemma 2.4 — powers stabilize in a groupfree semigroup
-- statement:
--   Let $S$ be a finite groupfree semigroup and $n>|S|$. Then for every $b\in S$ and every $m>n$,
--
--   $$
--   b^{m}=b^{m+1}.
--   $$
--
--   So every element of a finite groupfree semigroup has a power that absorbs further multiplication by the element, uniformly past $|S|$. This is what makes the languages $L(S,a)$ noncounting.
--
--   Differences from the source:
--   - encoding: b^m with an integer exponent m > n → the exponent m in the positive naturals; reason: m > n > |S| ≥ 0 forces m ≥ 1, and a semigroup has no b^0
-- source:
--   Chandra, Fortune, Lipton, Unbounded Fan-in Circuits and Associative Functions, STOC 1983, doi:10.1145/800061.808732, proof of Lemma 2.4, p.55

import Definitions.Def_FanInSemigroup_wordProd
import Definitions.Def_FanInSemigroup_IsGroupfree

set_option autoImplicit false

namespace FanInSemigroup

/-- **Claim in the proof of Lemma 2.4.** Chandra, Fortune, Lipton, STOC 1983, p.55: "Let n > |S|."
and "We first claim that for any b∈S, if m > n then b^m = b^{m+1}.", with `S` groupfree. -/
theorem ppow_stabilizes {S : Type*} [Semigroup S] [Finite S] (hS : IsGroupfree S) (n : ℕ)
    (hn : Nat.card S < n) (b : S) (m : ℕ+) (hm : n < m) : ppow b m = ppow b (m + 1) := by sorry

end FanInSemigroup
