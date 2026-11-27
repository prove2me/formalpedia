-- Prove2me | Theorems.Thm_DirectedHamiltonicity_Main_compile_cycle_search_controller
-- name    : DirectedHamiltonicity.Main.compile_cycle_search_controller
-- status  : Proved
-- author  : @Soh Kumabe
-- created : 2026-11-27T03:36:24.303857+00:00
-- url     : https://prove2.me/theorems/97c35194-cd40-5691-b9d1-4f250f52ec87
-- title:
--   Compilation of bounded adaptive parity calls into one log-cost RAM program
-- statement:
--   A bounded finite outer program that realizes the specified cycle search compiles to one native Prove2Me log-cost RAM with polynomial overhead. The native proof includes relocation, private arithmetic registers, random-access guest input, bounded coin windows, epoch-separated guest memory, and the final halt and output on arbitrary tapes.
-- source:
--   T. Koana and S. Kumabe, Breaking the 2^n barrier for directed hamiltonicity, Section 2, proof of Theorem 1. https://arxiv.org/html/2609.39062v2#S2

import Definitions.Def_DirectedHamiltonicity_CycleController

open TargetedSamplers DirectedHamiltonicity.Main.CycleReduction DirectedHamiltonicity.Main.CycleReduction.OuterMachine

theorem DirectedHamiltonicity.Main.compile_cycle_search_controller (Q : Program) (A k : ℕ) : BoundedController Q A k → ExecutesSearch Q A k := by sorry
