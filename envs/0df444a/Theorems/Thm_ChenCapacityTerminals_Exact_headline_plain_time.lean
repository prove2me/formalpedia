-- Prove2me | Theorems.Thm_ChenCapacityTerminals_Exact_headline_plain_time
-- name    : ChenCapacityTerminals.Exact.headline_plain_time
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T04:22:47.430832+00:00
-- url     : https://prove2.me/theorems/02845d05-1565-4d67-b451-c05e199c2653
-- title:
--   Theorem 1.1 — ordinary deterministic almost-linear-times-square-root algorithm
-- statement:
--   There is one ordinary deterministic bounded-word scalar program, with no flow-oracle instruction, which returns an exact rooted or global minimum entering shore. For every fixed polynomial input-size and capacity class and every $\varepsilon>0$, its running time is bounded uniformly by
--   $$
--   C\left((m+n)^{1+\varepsilon}\sqrt n+\widetilde O(m_{\rm in}+n)\right),
--   $$
--   where $m$ counts the positive coalesced loopless support and $m_{\rm in}$ counts raw records. The program precedes $\varepsilon$ and the instance.
--
--   This is the unconditional-time half of Theorem 1.1. Its proof combines the fixed-pair reduction with the deterministic almost-linear integer maximum-flow algorithm of van den Brand et al.
-- source:
--   Thomas Y. Chen, STOC 2027 submission #665, Theorem 1.1, paper pp. 1 and 9 (PDF pp. 2 and 10), final paragraph of the proof and §4.1; external dependency: van den Brand et al., FOCS 2023, Theorem 1.1; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/665.pdf#page=10

import Definitions.Def_ChenCapacityTerminals_Exact_Specifications

set_option autoImplicit false

theorem ChenCapacityTerminals.Exact.headline_plain_time :
    ∃ P : List TrulySubcubicAPSP.Instr,
      ChenCapacityTerminals.Exact.HeadlineTime P := by sorry
