-- Prove2me | Theorems.Thm_DirectedHamiltonicity_Main_read_cycle_graph_ram
-- name    : DirectedHamiltonicity.Main.read_cycle_graph_ram
-- status  : Proved
-- author  : @Soh Kumabe
-- created : 2026-11-27T02:32:13.011594+00:00
-- url     : https://prove2.me/theorems/06a47b5c-340a-4f4a-8919-7ec4287155bc
-- title:
--   Reading the directed cycle graph from its binary input tape on the log-cost RAM
-- statement:
--   One fixed native program fragment reads the self-delimiting vertex count and the row-major adjacency bits from the actual input tape, including the cases n = 0 and n = 1. Its output registers contain n and a word representing every ordered arc. It uses quadratically many primitive instructions, has a quadratic word-width bound, and preserves the caller's high registers.
-- source:
--   T. Koana and S. Kumabe, Breaking the 2^n barrier for directed hamiltonicity, Section 2, proof of Theorem 1. https://arxiv.org/html/2609.39062v2#S2

import Definitions.Def_DirectedHamiltonicity_Main_Algorithms
import Definitions.Def_LogCostRAM_StructuredExecution

open TargetedSamplers TargetedSamplers.Structured DirectedHamiltonicity.Main

theorem DirectedHamiltonicity.Main.read_cycle_graph_ram :
    ∃ code : Cmd, ∀ (n : ℕ) (adj : Fin n → Fin n → Bool) (coins : List Bool) (b : ℕ) (s : Store),
      s.mem 0 = 0 → s.Fits b → 8*(n+1)^2 ≤ b →
      ∃ t k, Exec (runTapes (encodeDigraph n adj) coins) (fun u => u.Fits b) code s t k ∧
        k ≤ 10*n.size+4*n+9*(n*n)+12 ∧ t.mem 1 = n ∧
        (∀ u v : Fin n, (t.mem 4).testBit (v.val+n*u.val) = adj u v) ∧ t.out = s.out ∧
        ∀ a ≥ 8, t.mem a = s.mem a := by sorry
