-- Prove2me | Theorems.Thm_DirectedHamiltonicity_Main_cycle_iff_closing_path
-- name    : DirectedHamiltonicity.Main.cycle_iff_closing_path
-- status  : Proved
-- author  : @Soh Kumabe
-- created : 2026-11-27T01:42:39.614088+00:00
-- url     : https://prove2.me/theorems/1f94b863-0669-4bc5-900d-d9f3424d6327
-- title:
--   Cutting a directed Hamiltonian cycle at its closing arc
-- statement:
--   In a directed graph on at least two vertices, a Hamiltonian cycle exists if and only if there are distinct vertices $s,t$ joined by a closing arc $t\to s$ such that an $s$–$t$ Hamiltonian path survives deletion of all loops, arcs entering $s$, and arcs leaving $t$. The input may contain loops.
-- source:
--   T. Koana and S. Kumabe, Breaking the 2^n barrier for directed hamiltonicity, Section 2, proof of Theorem 1. https://arxiv.org/html/2609.39062v2#S2

import Mathlib
import Definitions.Def_DirectedHamiltonicity_Main_Graphs

open DirectedHamiltonicity.Main

open Classical in
theorem DirectedHamiltonicity.Main.cycle_iff_closing_path {n : ℕ} (hn : 2 ≤ n) (adj : Fin n → Fin n → Bool) :
    HasHamCycle n adj ↔ ∃ s t : Fin n, s ≠ t ∧ adj t s = true ∧
      ((ofAdj (fun u v => adj u v = true ∧ u ≠ v ∧ v ≠ s ∧ u ≠ t)).hamPaths s t).Nonempty := by sorry
