-- Prove2me | Theorems.Thm_FairShareAlmostAll_Slack_Supplement_no_five_target_bundles
-- name    : FairShareAlmostAll.Slack.Supplement.no_five_target_bundles
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:15:54.979461+00:00
-- url     : https://prove2.me/theorems/1c7ad034-176c-4df3-ada0-ee94e92f6b90
-- title:
--   Claim 5.1 — No five disjoint bundles of value $153$
-- statement:
--   For the thirteen goods with values $(137,135,119,79,77,76,54,50,49,10,9,8,6)$, there are no five pairwise disjoint bundles $B_1,\dots,B_5\subseteq G$ with
--
--   $$v(B_j)\ge153\qquad(1\le j\le5).$$
--
--   The bundles are arbitrary subsets of $G$, not only bundles of the table, and need not cover $G$. Together with Observation 5.1 this is the obstruction behind Proposition 5.1.
--
--   Differences from the source:
--   - encoding: five bundles $B_1,\dots,B_5$ over goods $1,\dots,13$ → a family `Fin 5 → Finset (Fin 13)` that is pairwise disjoint, conclusion "some bundle has value $<153$"; reason: the contrapositive of the source's nonexistence, with relabeled goods
-- source:
--   Tomer Ezra, Tamar Garbuz, Fair Share Allocations for Almost All Agents, STOC 2027 submission #480 (October 2026), printed pp. 20–21 (PDF pp. 21–22), Claim 5.1 and proof; source.pdf SHA256 c9f47a54f6a9e1568951e8e3845ff79c34d51d391a68fd697d37d8ba29cc7491

import Mathlib
import Definitions.Def_AnyPriceShare_Bidding_Basic
import Definitions.Def_FairShareAlmostAll_Slack_FiniteAllocation
import Definitions.Def_FairShareAlmostAll_Slack_Supplement_ThirteenGoods

namespace FairShareAlmostAll.Slack.Supplement

open FairShareAlmostAll.Slack AnyPriceShare.Bidding

theorem no_five_target_bundles (B : Fin 5 → Finset (Fin 13)) (hB : PartialAllocation B) :
    ∃ j, addVal thirteenValue (B j) < 153 := by sorry

end FairShareAlmostAll.Slack.Supplement
