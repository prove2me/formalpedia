-- Prove2me | Theorems.Thm_FanInSemigroup_lemma_2_4
-- name    : FanInSemigroup.lemma_2_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:33:35.971552+00:00
-- url     : https://prove2.me/theorems/c42f02d5-f8af-4ae4-89ff-10bb07ef6363
-- title:
--   Lemma 2.4 — $L(S,a)$ is noncounting for groupfree $S$
-- statement:
--   Let $S$ be a finite groupfree semigroup. Then for every $a\in S$ the language $L(S,a)$ is noncounting: there is an $n$ such that for all words $x,y,z$ over $S$, the empty word included, and all $m\ge n$, we have $xy^mz\in L(S,a)$ if and only if $xy^{m+1}z\in L(S,a)$.
--
--   Together with Theorem 2.5 this makes $L(S,a)$ accepted by an rs machine.
--
--   Differences from the source:
--   - encoding: "noncounting" is defined for regular sets → IsNoncounting does not include regularity; reason: the regularity of L(S,a) is the separate milestone wordLanguage_isRegular
-- source:
--   Chandra, Fortune, Lipton, Unbounded Fan-in Circuits and Associative Functions, STOC 1983, doi:10.1145/800061.808732, Lemma 2.4, p.55

import Definitions.Def_FanInSemigroup_wordLanguage
import Definitions.Def_FanInSemigroup_IsGroupfree
import Definitions.Def_FanInSemigroup_IsNoncounting

set_option autoImplicit false

namespace FanInSemigroup

/-- **Lemma 2.4.** Chandra, Fortune, Lipton, STOC 1983, p.55: "Suppose S is group free. Then for
any a in S, L(S,a) is noncounting." -/
theorem lemma_2_4 {S : Type*} [Semigroup S] [Finite S] (hS : IsGroupfree S) (a : S) :
    IsNoncounting (wordLanguage a) := by sorry

end FanInSemigroup
