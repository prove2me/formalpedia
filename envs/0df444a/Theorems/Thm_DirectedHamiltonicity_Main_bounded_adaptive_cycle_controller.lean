-- Prove2me | Theorems.Thm_DirectedHamiltonicity_Main_bounded_adaptive_cycle_controller
-- name    : DirectedHamiltonicity.Main.bounded_adaptive_cycle_controller
-- status  : Proved
-- author  : @Soh Kumabe
-- created : 2026-11-27T03:41:46.430567+00:00
-- url     : https://prove2.me/theorems/fc84ce80-768c-45f7-84ae-57f4542d662c
-- title:
--   The bounded outer register program for one-sided directed-cycle search
-- statement:
--   Carry out the specified adaptive edge deletions, dyadic trial choices, repeated parity votes and final orbit check in a finite controller with polynomial word lengths. The source semantics charge each candidate call its full bound and use the exact finite coin tape of the input. The output must agree with the finite cycle search on every tape
-- source:
--   RAM implementation step for the finite search in T. Koana and S. Kumabe, Breaking the 2^n barrier for directed hamiltonicity, proof of Theorem 1. https://arxiv.org/html/2609.39062v2#S2

import Definitions.Def_DirectedHamiltonicity_CycleController

open TargetedSamplers DirectedHamiltonicity.Main.CycleReduction DirectedHamiltonicity.Main.CycleReduction.OuterMachine

theorem DirectedHamiltonicity.Main.bounded_adaptive_cycle_controller (Q : Program) (A k : ℕ) :
    QueryTime Q A k → BoundedController Q A k := by sorry
