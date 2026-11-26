-- Prove2me | Theorems.Thm_DirectedHamiltonicity_Main_InputRAM_preprocess_exec
-- name    : DirectedHamiltonicity.Main.InputRAM.preprocess_exec
-- status  : Proved
-- author  : @Soh Kumabe
-- created : 2026-11-26T17:20:22.292444+00:00
-- url     : https://prove2.me/theorems/4dac8e2c-8afe-5180-ae48-dc191a02ec03
-- title:
--   Computing the incoming-weight degree and trial schedule on the RAM
-- statement:
--   Suppose the RAM store contains the parsed records of a weighted directed multigraph with $n$ vertices and $m$ arcs, its endpoints and its target. Let $W$ be the largest input weight, let $d$ be the sampling degree of the normalized graph, and let $K(n,d)$ be the specified sampling block size.
--
--   If the store fits in width $b$ and this width accommodates $W+1$ and the schedule, preprocessing retains the arc records and endpoints in the graph view and records $d$, the saved target word and the trial count
--
--   $$M=K(n,d)(n+4).$$
--
--   Writing $S(n,d)$ for the schedule subroutine's primitive step bound, preprocessing takes at most
--
--   $$n\big((W+1)(n(18m+20)+8)+8\big)+S(n,d)+16$$
--
--   steps. Every intermediate word fits the same width bound. The program preserves the output string and leaves memory above the input table zero.
-- source:
--   Auxiliary result for the log-cost RAM formalization of Proposition 4 in T. Koana and S. Kumabe, Breaking the 2^n barrier for directed hamiltonicity, STOC 2027 submission 811, PDF pp. 5 and 8–11. https://prove2.me/theorems/aa04b14a-8225-48c8-904c-8725ebdcac66

import Definitions.Def_DirectedHamiltonicity_ParityRAMInterfaces

open DirectedHamiltonicity DirectedHamiltonicity.Main DirectedHamiltonicity.Main.InputRAM
open TargetedSamplers TargetedSamplers.Structured TargetedSamplers.Structured.Word
open Multidigraph Classical

theorem DirectedHamiltonicity.Main.InputRAM.preprocess_exec {τ : Tapes} {b n m : ℕ} {tail head : Fin m → Fin n} {w : Fin m → ℕ}
    {s t : Fin n} {B : ℤ} (u : Store) (h : Parsed tail head w s t B u) (fit : u.Fits b) :
    let W := Finset.univ.sup w
    let hw : ∀ e, w e ≤ W := fun e => Finset.le_sup (Finset.mem_univ e)
    let H : Multidigraph (Fin n) (Fin m) := ⟨tail,head⟩
    let G := Multidigraph.normalizedGraph H w s t hw
    let p := Multidigraph.normalizedWeight H w s t hw
    let d := Multidigraph.samplingDegree G p
    (W+1).size ≤ b → scheduleWidth n d ≤ b →
    ∃ z j, Exec τ (fun v => v.Fits b) preprocess u z j ∧ j ≤ preprocessWork n m W d ∧
      GraphView (W := W) tail head w s t graphBase z ∧ z.mem 52 = d ∧ z.mem 53 = u.mem 1 ∧
      z.mem 54 = samplingBlockSize n d*(n+4) ∧ z.out = u.out ∧
      ∀ a ≥ graphBase+(3*m+2), z.mem a=0 := by sorry
