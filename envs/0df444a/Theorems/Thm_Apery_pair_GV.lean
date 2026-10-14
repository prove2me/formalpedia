-- Prove2me | Theorems.Thm_Apery_pair_GV
-- name    : Apery.pair_GV
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-12T21:47:05.535732+00:00
-- url     : https://prove2.me/theorems/6956500c-5e71-4c94-97db-77355204f936
-- title:
--   The pairing lemma: two remaining poles $a, p-a$ give an integral contribution
-- statement:
--   **The pairing lemma (4.5).** Let $3 \le p$, $1 \le a < p$ with $a \ne p - a$, let $M$ be a multiset of integers containing every $i \in [1, K]$ with $i \ne a,\ p-a$, and suppose the residue $res_K(tpol\,M)(p-a)$ has valuation $\ge -1$. Then $res_K(tpol\,M)(a)\cdot poleValue(a) + res_K(tpol\,M)(p-a)\cdot poleValue(p-a)$ is $p$-integral in the Gauss valuation. This is `pair_GV` of `Apery/Arith/OuterEntries.lean`: the two remaining poles of the same class in the outer-range entry contribute an integral amount. It is used by the pole case analysis of `Apery.outer_entry`.
-- source:
--   https://github.com/mo271/Zeta5/blob/7fe736760f4b96bfdb4334b68e3b3124ecbe10b0/Apery/Arith/OuterEntries.lean#L202-L279

import Mathlib
import Definitions.Def_Zeta5_SourceConstruction
import Definitions.Def_Zeta5_SourceArith
import Definitions.Def_Zeta5_SourceGrowthTables
import Definitions.Def_Zeta5_SourceInner
import Definitions.Def_Zeta5_SourceOuter
import Definitions.Def_Zeta5_SourcePoleFun
import Definitions.Def_Zeta5_SourcePullback
import Definitions.Def_Zeta5_SourceValToolkit

open Finset Polynomial

namespace Apery

theorem pair_GV {p : ℕ} [hp : Fact p.Prime] (hp3 : 3 ≤ p) {K : ℕ} (M : Multiset ℤ) {a : ℕ}
    (ha1 : 1 ≤ a) (hap : a < p) (hne : a ≠ p - a) (haK : a ≤ K) (hbK : p - a ≤ K)
    (hroots : ∀ i ∈ Icc 1 K, i ≠ a → i ≠ p - a → (i : ℤ) ∈ M)
    (hres : VG p (res K (tpol M) (p - a)) (-1)) :
    GV p (C (res K (tpol M) a) * poleValue a +
      C (res K (tpol M) (p - a)) * poleValue (p - a)) 0 := by
  sorry

end Apery
