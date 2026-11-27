-- Prove2me | Theorems.Thm_DirectedHamiltonicity_Main_prepare_cycle_parity_query_ram
-- name    : DirectedHamiltonicity.Main.prepare_cycle_parity_query_ram
-- status  : Proved
-- author  : @Soh Kumabe
-- created : 2026-11-27T02:28:06.064079+00:00
-- url     : https://prove2.me/theorems/a65a7f36-fd80-4bb1-8c75-6ec6fb6fb1a9
-- title:
--   A log-cost RAM subroutine that constructs the encoded weighted Hamiltonian-path query
-- statement:
--   A single relocatable RAM subroutine takes the number of vertices, the adjacency word, and a trial rank from caller registers. It returns the exact serialized query in one sentinel-terminated binary word and preserves the caller's high registers and output. A fixed polynomial bounds the number of native instructions and a fixed polynomial supplies a sufficient word width.
-- source:
--   T. Koana and S. Kumabe, Breaking the 2^n barrier for directed hamiltonicity, Section 2, proof of Theorem 1. https://arxiv.org/html/2609.39062v2#S2

import Definitions.Def_DirectedHamiltonicity_CycleSearch
import Definitions.Def_LogCostRAM_StructuredExecution

open DirectedHamiltonicity.Main DirectedHamiltonicity.Main.CycleReduction
open TargetedSamplers TargetedSamplers.Structured Word BinaryStack

theorem DirectedHamiltonicity.Main.prepare_cycle_parity_query_ram :
    ∃ (floor : ℕ) (code : ℕ → Cmd) (room steps : Polynomial ℕ),
      ∀ (bank w n a r : ℕ) (adj : Fin n → Fin n → Bool) (τ : Tapes) (s : Store) (b : ℕ),
        floor ≤ bank → room.eval w ≤ b → s.Fits b → n ≤ w → n < 2^w → a < 2^w → r < 2^w →
        (∀ u v : Fin n, a.testBit (v.val+n*u.val) = adj u v) →
        s.mem (cell bank) = n → s.mem (cell (bank+1)) = a → s.mem (cell (bank+2)) = r →
        s.mem (cell (bank+3)) = 2^w →
        ∃ t k, Exec τ (fun v => v.Fits b) (code bank) s t k ∧ k ≤ steps.eval b ∧
          t.mem 0 = packed (if h : r < drawCount n then
            (candidateInput adj ((rankDraw n).symm ⟨r,h⟩)).getD [] else []) ∧
          t.out = s.out ∧ ∀ i ≥ floor, t.mem (cell i) = s.mem (cell i) := by sorry
