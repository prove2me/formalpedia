-- Prove2me | Theorems.Thm_FairShareAlmostAll_Slack_Supplement_fractional_certificate
-- name    : FairShareAlmostAll.Slack.Supplement.fractional_certificate
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-15T19:15:27.34432+00:00
-- url     : https://prove2.me/theorems/5f2222be-dfb3-41fb-a034-f8812ac8186f
-- title:
--   Observation 5.1 — Fractional certificate for the thirteen-goods instance
-- statement:
--   For the thirteen goods $G=\{1,\dots,13\}$ with values $(137,135,119,79,77,76,54,50,49,10,9,8,6)$ and the weighted bundle family $\mathcal Q$ of the paper's table, every bundle $P\in\mathcal Q$ has value $v(P)\ge153$, and
--
--   $$\sum_{P\in\mathcal Q}\tau_P=\frac{51}{10},\qquad \ell_g=\sum_{P\in\mathcal Q,\ g\in P}\tau_P=1\quad(g\in G).$$
--
--   Scaled by an entitlement, these weights form an APS certificate for target $153$; Proposition 5.1 extends them with singleton goods.
--
--   Differences from the source:
--   - encoding: goods $1,\dots,13$ → `Fin 13` with paper good $g$ at index $g-1$; reason: relabeling only
-- source:
--   Tomer Ezra, Tamar Garbuz, Fair Share Allocations for Almost All Agents, STOC 2027 submission #480 (October 2026), printed pp. 19–20 (PDF pp. 20–21), §5.1 table and Observation 5.1; source.pdf SHA256 c9f47a54f6a9e1568951e8e3845ff79c34d51d391a68fd697d37d8ba29cc7491

import Mathlib
import Definitions.Def_AnyPriceShare_Bidding_Basic
import Definitions.Def_FairShareAlmostAll_Slack_FiniteAllocation
import Definitions.Def_FairShareAlmostAll_Slack_Supplement_ThirteenGoods

namespace FairShareAlmostAll.Slack.Supplement

open FairShareAlmostAll.Slack AnyPriceShare.Bidding

theorem fractional_certificate :
    (∀ P : Fin 13, 153 ≤ addVal thirteenValue (thirteenBundle P)) ∧
    ∑ P : Fin 13, thirteenWeight P = 51 / 10 ∧
    ∀ g : Fin 13,
      ∑ P ∈ Finset.univ.filter (fun P : Fin 13 => g ∈ thirteenBundle P),
        thirteenWeight P = 1 := by sorry

end FairShareAlmostAll.Slack.Supplement
