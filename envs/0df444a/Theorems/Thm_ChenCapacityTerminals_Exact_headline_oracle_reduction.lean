-- Prove2me | Theorems.Thm_ChenCapacityTerminals_Exact_headline_oracle_reduction
-- name    : ChenCapacityTerminals.Exact.headline_oracle_reduction
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T04:21:43.453734+00:00
-- url     : https://prove2.me/theorems/0f946660-8411-4536-a728-4e135c2765c6
-- title:
--   Theorem 1.1 — deterministic fixed-pair oracle reduction
-- statement:
--   There is one deterministic bounded-word oracle program which solves both rooted and global directed minimum cut. For every fixed polynomial bound on raw arc count and capacities, the program returns an exact optimal shore and satisfies the headline guarantees: total submitted-network volume and outside work are $\widetilde O((m+n)\sqrt n)$ (with raw preprocessing included in outside work), there are $\widetilde O(\sqrt n)$ calls, and every call has $O(n)$ vertices and $O(m+n)$ arcs. All guarantees hold for every lawful integral flow-and-shore oracle, independently of its tie-breaking.
--
--   This is the fixed-pair-reduction half of Theorem 1.1; the ordinary scalar running-time assertion is treated separately.
-- source:
--   Thomas Y. Chen, STOC 2027 submission #665, Theorem 1.1 and its proof, paper pp. 1 and 9 (PDF pp. 2 and 10), especially the dyadic schedule and Eq. (6); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/665.pdf#page=10

import Definitions.Def_ChenCapacityTerminals_Exact_Specifications

set_option autoImplicit false

theorem ChenCapacityTerminals.Exact.headline_oracle_reduction :
    ∃ P : ChenCapacityTerminals.Exact.WordProgram,
      ChenCapacityTerminals.Exact.HeadlineReduction P := by sorry
