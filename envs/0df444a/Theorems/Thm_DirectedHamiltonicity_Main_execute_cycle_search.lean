-- Prove2me | Theorems.Thm_DirectedHamiltonicity_Main_execute_cycle_search
-- name    : DirectedHamiltonicity.Main.execute_cycle_search
-- status  : Proved
-- author  : @Soh Kumabe
-- created : 2026-11-27T02:11:53.315352+00:00
-- url     : https://prove2.me/theorems/c17e5181-719c-478a-b498-cf428e0d403d
-- title:
--   Realizing the finite directed-cycle oracle search on a log-cost RAM
-- statement:
--   Given a fixed log-cost RAM whose candidate calls always halt with a one-bit result within the declared allowance, realize the explicit finite-tape edge-deletion and cycle-verification algorithm on a single log-cost RAM. The host machine must implement the exact per-tape result, with polynomial overhead in the number of vertices over the aggregate call and tape budgets.
-- source:
--   RAM implementation step for the finite search in T. Koana and S. Kumabe, Breaking the 2^n barrier for directed hamiltonicity, proof of Theorem 1. https://arxiv.org/html/2609.39062v2#S2

import Definitions.Def_DirectedHamiltonicity_CycleSearch

open TargetedSamplers DirectedHamiltonicity.Main.CycleReduction

theorem DirectedHamiltonicity.Main.execute_cycle_search (Q : Program) (A k : ℕ)
    (bounded : QueryTime Q A k) : ExecutesSearch Q A k := by sorry
