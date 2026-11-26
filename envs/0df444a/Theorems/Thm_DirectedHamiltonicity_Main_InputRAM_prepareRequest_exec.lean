-- Prove2me | Theorems.Thm_DirectedHamiltonicity_Main_InputRAM_prepareRequest_exec
-- name    : DirectedHamiltonicity.Main.InputRAM.prepareRequest_exec
-- status  : Proved
-- author  : @Soh Kumabe
-- created : 2026-11-26T17:40:31.006861+00:00
-- url     : https://prove2.me/theorems/1dc9633b-0587-4151-8fd7-d29cb3859954
-- title:
--   Packing a weighted graph and initializing the RAM query registers
-- statement:
--   A graph view contains $n$ vertices, $m$ labelled arcs of weights at most $W$, and two distinguished endpoints. Let $M$ be the scheduled number of trials and $D$ the saved target. The finite RAM subroutine constructs a request whose graph argument encodes the normalized Boolean adjacency grid of length
--
--   $$N=n^2(W+1).$$
--
--   Assume the caller's bank is above the reserved registers, the initial store fits width $b$, and the grid addresses, argument width and report cap $12M$ fit the specified bounds. The resulting request contains the graph dimensions, endpoints, packed adjacency word, trial budget and target. Let $h$ be the chosen request field width, let $F$ be the fixed length of the register-initialization circuit, and put $L=b(5b+9)+15$. The execution takes at most
--
--   $$6L+N(5L+18m+19)+14N+16+(h+F)L$$
--
--   primitive steps. The output and every cell beyond both the bank and the grid are preserved.
-- source:
--   Auxiliary result for the log-cost RAM formalization of Proposition 4 in T. Koana and S. Kumabe, Breaking the 2^n barrier for directed hamiltonicity, STOC 2027 submission 811, PDF pp. 5 and 8–11. https://prove2.me/theorems/aa04b14a-8225-48c8-904c-8725ebdcac66

import Definitions.Def_DirectedHamiltonicity_ParityRAMInterfaces

open DirectedHamiltonicity DirectedHamiltonicity.Main DirectedHamiltonicity.Main.InputRAM
open Multidigraph NativeGraph TargetedSamplers TargetedSamplers.Structured TargetedSamplers.Structured.Word
open TargetedSamplers.Structured.BinaryStack

theorem DirectedHamiltonicity.Main.InputRAM.prepareRequest_exec {τ : Tapes} {b n m W raw : ℕ} {tail head : Fin m → Fin n} {w : Fin m → ℕ}
    (hw : ∀ e, w e ≤ W) {s t : Fin n} (bank M D : ℕ) (u : Store)
    (view : GraphView (W := W) tail head w s t raw u) (trials : u.mem 54=M) (target : u.mem 53=D)
    (high : 60 ≤ cell bank) (fit : u.Fits b) (hb : 2 ≤ b) :
    let H : Multidigraph (Fin n) (Fin m) := ⟨tail,head⟩
    let wbits := argumentWidth n (W+1)
    let N := n*(n*(W+1))
    let dst := raw+3*m+2
    let L := b*(5*b+9)+15
    (dst+2*N+2*n+2).size ≤ b → wbits+2 ≤ b → (12*M).size ≤ b →
    ∃ z j, Exec τ (fun v => v.Fits b) (prepareRequest bank) u z j ∧
      j ≤ 6*L+N*(5*L+18*m+19)+14*N+16+(wbits+initFields.length)*L ∧
      PreparedRequest (cell bank) n (W+1) s.val t.val (packed (adjacencyBits H w hw s t)) M D (dst+N) z ∧
      z.out=u.out ∧ ∀ i, cell bank+68 < i → dst+N ≤ i → z.mem i=u.mem i := by sorry
