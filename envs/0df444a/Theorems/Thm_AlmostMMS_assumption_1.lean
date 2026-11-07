-- Prove2me | Theorems.Thm_AlmostMMS_assumption_1
-- name    : AlmostMMS.assumption_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:48:21.882478+00:00
-- url     : https://prove2.me/theorems/e9b9bba5-9d97-4964-b756-c55c62c74651
-- title:
--   Assumption 1 — reduction to ordered instances with bundles of value one
-- statement:
--   Let $v$ be additive with $\mathrm{MMS}(M,v_i,d)=1$ for all $i$, and $d\ge1$. Then there is an ordered instance $J$, with the same agents and number of items, whose values lie in $[0,1]$, are non-increasing along a common order, and whose $d$ bundles have value exactly $1$, such that the following holds. For every set $I$ of agents and every allocation $A'$ of the items of $J$ to $I$, there is an allocation $A$ of the items of the original instance to $I$ with
--   $$
--   \sum_{e:\,A'(e)=i}J.v_i(e)\le v_i(A_i)\qquad\text{for every } i\in I.
--   $$
--   So a guarantee for ordered instances transfers to all instances. The paper states the three properties as "without loss of generality" and cites [BL16] for the order.
--
--   Differences from the source:
--   - reading: "Without loss of generality … we can assume" three bullets (with the citation [BL16]) → a transfer statement: an ordered instance J and a conversion of allocations; reason: the page states no theorem; this is the claim the reduction delivers and the proof of Theorem 3.1 uses
--   - encoding: additive valuations with v(∅) = 0, monotone → the published `LittleCharity.MMS.IsAdditive` (additivity and nonnegativity); reason: equivalent for additive set functions
-- source:
--   Feige, Grinberg, Almost-MMS allocations with small agent redundancy, STOC 2027 submission, arXiv:2611.05360 (manuscript sha256 3925c4ab…), Assumption 1, p.3

import Mathlib
import Definitions.Def_LittleCharity_MMS_Setting
import Definitions.Def_AlmostMMS_OrderedInstance

namespace AlmostMMS

open Finset

/-- **Assumption 1, p.3, as a transfer statement.** Feige, Grinberg, *Almost-MMS allocations with small agent redundancy*, STOC 2027 submission,
arXiv:2611.05360 (manuscript sha256 3925c4ab…): without loss of generality item
values are in `[0, 1]`, each agent's witnessing `d`-partition has bundles of value exactly `1`, and all
agents order the items alike ([BL16]).

**Formalization Note.** The paper's "without loss of generality" is stated as what it delivers: from an
additive instance with `MMS(M, v_i, d) = 1` one gets an ordered instance `J` such that every allocation
`A'` of the items to a set `I` of agents in `J` converts to an allocation `A` to the same `I` in the
original instance that gives each agent of `I` at least the value that agent had under `J`. -/
theorem assumption_1 {n m d : ℕ} (v : Fin n → Finset (Fin m) → ℝ)
    (hv : LittleCharity.MMS.IsAdditive v) (hd : 1 ≤ d)
    (hmms : ∀ i, LittleCharity.MMS.mms (v i) d univ = 1) :
    ∃ J : OrderedInstance n m d, ∀ (I : Finset (Fin n)) (A' : Fin m → Fin n), (∀ e, A' e ∈ I) →
      ∃ A : Fin m → Fin n, (∀ e, A e ∈ I) ∧
        ∀ i ∈ I, ∑ e with A' e = i, J.v i e ≤ v i (univ.filter fun b => A b = i) := by sorry

end AlmostMMS
