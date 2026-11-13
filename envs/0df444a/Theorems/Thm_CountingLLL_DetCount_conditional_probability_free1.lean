-- Prove2me | Theorems.Thm_CountingLLL_DetCount_conditional_probability_free1
-- name    : CountingLLL.DetCount.conditional_probability_free1
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T04:43:46.199096+00:00
-- url     : https://prove2.me/theorems/5c54063c-02ec-45d0-b845-451f7acb12a9
-- title:
--   Lemma 4.2: conditioning on nearby free constraints
-- statement:
--   Let $T$ be a rooted 2-tree in the dependency graph of a constraint family $E$. If the probability of satisfying $\mathrm{free}(T)$ is positive, the probability that every constraint in $T$ is violated conditioned on satisfying all of $\mathrm{free}(T)$ equals the same conditional probability with only $\mathrm{free}^{(1)}(T)$, the free constraints at graph distance one, in the conditioning event. This is the conditional-probability clause of Lemma 4.2; the positive-denominator hypothesis makes the conditioning explicit.
-- source:
--   Hongyang Liu, Chunyang Wang, Yitong Yin, Yiyao Zhang, Can Zhou, A Counting and Sampling Lovász Local Lemma, STOC 2027 submission #442, Lemma 4.2 and proof, PDF p. 13 (printed p. 12); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Definitions.Def_CountingLLL_DetCount_Expansion

set_option autoImplicit false

namespace CountingLLL.DetCount
open CSP
theorem conditional_probability_free1 (Φ : CSP) (E T : Finset (Fin Φ.m)) (r : Fin Φ.m)
    (hT : T ∈ Φ.twoTrees E r) (hpos : 0 < Φ.prob (Φ.SatAll (Φ.free E r T))) :
    Φ.treeCoeff E r T = Φ.condProb (Φ.ViolAll T) (Φ.SatAll (Φ.free1 E r T)) := by sorry
end CountingLLL.DetCount
