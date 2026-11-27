-- Prove2me | Theorems.Thm_DirectedHamiltonicity_Main_CycleHost_readGraph_exec
-- name    : DirectedHamiltonicity.Main.CycleHost.readGraph_exec
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-27T04:02:16.182246+00:00
-- url     : https://prove2.me/theorems/5a12adc3-611a-4152-b921-c69e0b20eccc
-- title:
--   Host sub-routine: reading the adjacency matrix
-- statement:
--   Specification of the sub-routine `readGraph`.
--
--   When the input tape is the encoding of an $n$-vertex adjacency matrix $\mathrm{adj}$ and the cursor register points just after the header, the routine reads the $n^2$ matrix bits in row-major order in at most $100(n+1)^2$ steps and leaves in register $G$ a number
--   $$G<2^{n^2},\qquad \text{bit } un+v \text{ of } G = \mathrm{adj}(u,v).$$
--   Only its listed scratch registers change.
-- source:
--   Engineering lemma for DirectedHamiltonicity.Main.execute_cycle_search: specification of a sub-routine of the host program in Def_DirectedHamiltonicity_CycleSearchHost, supporting Theorem 1 of T. Koana and S. Kumabe, Breaking the 2^n barrier for directed hamiltonicity (STOC 2027 submission #811), Section 2 (PDF pp. 4-5).

import Definitions.Def_DirectedHamiltonicity_CycleSearchHost

open TargetedSamplers TargetedSamplers.Structured TargetedSamplers.Structured.Word
open TargetedSamplers.Structured.Interp DirectedHamiltonicity.Main.CycleReduction
open DirectedHamiltonicity.Main.CycleHost

theorem DirectedHamiltonicity.Main.CycleHost.readGraph_exec {τ : Tapes} {b : ℕ} (u : Store) {n : ℕ} (adj : Fin n → Fin n → Bool)
    (hin : τ.input = encodeDigraph n adj)
    (c : Consts u) (rn : u.mem (cell rN) = n) (rn2 : u.mem (cell rN2) = n * n)
    (rcur : u.mem (cell rCur) = 2 * n.size + 1)
    (fit : u.Fits b) (hb : 64 * (n + 1) ^ 3 ≤ b) :
    ∃ v j, Exec τ (fun w => w.Fits b) readGraph u v j ∧ j ≤ 100 * (n + 1) ^ 2 ∧
      v.mem (cell rG) < 2 ^ (n * n) ∧
      (∀ x y : Fin n, (v.mem (cell rG)).testBit (x.val * n + y.val) = adj x y) ∧
      Kept readGraphDirty u v (fun _ => True) := by sorry
