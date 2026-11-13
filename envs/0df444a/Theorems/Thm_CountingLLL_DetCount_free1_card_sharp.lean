-- Prove2me | Theorems.Thm_CountingLLL_DetCount_free1_card_sharp
-- name    : CountingLLL.DetCount.free1_card_sharp
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T04:43:41.76606+00:00
-- url     : https://prove2.me/theorems/33e56647-f3ac-4dcd-9cb6-a98667f0421f
-- title:
--   Lemma 4.2: sharp bound for nearby free constraints
-- statement:
--   Let $T$ be a rooted 2-tree in the dependency graph of a constraint family $E$, and let $D_E$ be the maximum dependency degree within $E$. Write $\mathrm{free}^{(1)}(T)$ for the free constraints at distance one from $T$. Then $|\mathrm{free}^{(1)}(T)| \le (D_E-1)|T|+1$. This is the cardinality clause of Lemma 4.2, stated for an arbitrary subfamily and its own degree. The integer inequality also covers $D_E=0$.
-- source:
--   Hongyang Liu, Chunyang Wang, Yitong Yin, Yiyao Zhang, Can Zhou, A Counting and Sampling Lovász Local Lemma, STOC 2027 submission #442, Lemma 4.2 and proof, PDF p. 13 (printed p. 12); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Definitions.Def_CountingLLL_DetCount_Expansion

set_option autoImplicit false

namespace CountingLLL.DetCount
open CSP
theorem free1_card_sharp (Φ : CSP) (E T : Finset (Fin Φ.m)) (r : Fin Φ.m)
    (hT : T ∈ Φ.twoTrees E r) :
    ((Φ.free1 E r T).card : ℤ) ≤ ((Φ.Dsub E : ℤ)-1) * T.card + 1 := by sorry
end CountingLLL.DetCount
