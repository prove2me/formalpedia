-- Prove2me | Theorems.Thm_DirectedHamiltonicity_Main_InputRAM_TrialParameters_runTrials_exec
-- name    : DirectedHamiltonicity.Main.InputRAM.TrialParameters.runTrials_exec
-- status  : Proved
-- author  : @Soh Kumabe
-- created : 2026-11-26T17:41:51.783936+00:00
-- url     : https://prove2.me/theorems/4b38b27d-7e16-518d-86b8-3047ffe920ad
-- title:
--   A per-tape RAM bound for capped affine sampling trials
-- statement:
--   Let $M$ be the trial budget, $E_i$ an optional affine system for trial $i$, and $f$ a binary contribution for each reported word. Assume the counting solver and graph queries satisfy their memory and time contracts. Start with an empty seen-word table, zero cursors and a store of sufficient word width.
--
--   When the total number of reports exceeds $12M$, the program appends zero to the output. Otherwise it appends the parity of the contributions of the distinct reported words. If $p$ and $v$ are the per-trial preparation/count and per-visit bounds, the primitive step count on every such tape is at most
--
--   $$M\big((p+4)+(p+5)+12(v+3)\big)+5.$$
-- source:
--   Auxiliary result for the log-cost RAM formalization of Proposition 4 in T. Koana and S. Kumabe, Breaking the 2^n barrier for directed hamiltonicity, STOC 2027 submission 811, PDF pp. 5 and 8–11. https://prove2.me/theorems/aa04b14a-8225-48c8-904c-8725ebdcac66

import Definitions.Def_DirectedHamiltonicity_ParityRAMInterfaces

open DirectedHamiltonicity DirectedHamiltonicity.Main DirectedHamiltonicity.Main.InputRAM
open TargetedSamplers TargetedSamplers.Structured TargetedSamplers.Structured.Word
open AffinePrefixEnumeration EditGV897.Main Multidigraph
open scoped BigOperators
open DirectedHamiltonicity DirectedHamiltonicity.Main DirectedHamiltonicity.Main.InputRAM DirectedHamiltonicity.Main.InputRAM.TrialParameters

theorem DirectedHamiltonicity.Main.InputRAM.TrialParameters.runTrials_exec {τ : Tapes} {b floor cost : ℕ} (P : TrialParameters) (S : Solver) (kernel : Cmd)
    (eqs : ℕ → Option (List (Equation P.dim))) (f : List Bool → ZMod 2)
    (space : P.Space S floor b) (oracle : P.Queries τ b floor cost kernel eqs f) (u : Store)
    (initial : P.invariant f ∅ u) (trial : u.mem (P.a+65)=0) (total : u.mem (P.a+68)=0) (fit : u.Fits b) :
    let p := P.countCost S b cost
    let v := P.visitCost S cost
    ∃ z k, Exec τ (fun y => y.Fits b) (runTrials P.bank kernel S.command) u z k ∧
      k ≤ P.trials*((p+4)+(p+5)+12*(v+3))+5 ∧ z.out=u.out++[P.estimate eqs f] := by sorry
