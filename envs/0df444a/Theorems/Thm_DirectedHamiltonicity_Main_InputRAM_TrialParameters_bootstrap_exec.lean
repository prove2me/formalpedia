-- Prove2me | Theorems.Thm_DirectedHamiltonicity_Main_InputRAM_TrialParameters_bootstrap_exec
-- name    : DirectedHamiltonicity.Main.InputRAM.TrialParameters.bootstrap_exec
-- status  : Proved
-- author  : @Soh Kumabe
-- created : 2026-11-26T17:27:01.085302+00:00
-- url     : https://prove2.me/theorems/b49afbdf-492b-55a2-96d0-ada6a698c737
-- title:
--   Initializing the affine workspace and shared random mask
-- statement:
--   Start with a prepared graph request, a zero-initialized upper memory range and a finite coin tape. Let $\ell$ be the mask length and $K$ the number of admissible coefficient tuples. The prescribed mask is the rank of the tape's first $\ell$ bits with zero extension. Assume a graph query returns $\ell$ and $K$ in its two initialization modes, with the stated cost and memory guarantees.
--
--   For sufficient word width and workspace separation, the RAM initializes the solver layout and establishes the trial invariant with the empty set of reported words. Both the trial cursor and the report total are zero. The initialization preserves the output string and satisfies the explicit step bound in the statement, including the two graph queries and the cost of reading the shared prefix.
-- source:
--   Auxiliary result for the log-cost RAM formalization of Proposition 4 in T. Koana and S. Kumabe, Breaking the 2^n barrier for directed hamiltonicity, STOC 2027 submission 811, PDF pp. 5 and 8–11. https://prove2.me/theorems/aa04b14a-8225-48c8-904c-8725ebdcac66

import Definitions.Def_DirectedHamiltonicity_ParityRAMInterfaces

open DirectedHamiltonicity DirectedHamiltonicity.Main DirectedHamiltonicity.Main.InputRAM
open TargetedSamplers TargetedSamplers.Structured TargetedSamplers.Structured.Word
open TargetedSamplers.Structured.BinaryStack FiniteSampling
open DirectedHamiltonicity DirectedHamiltonicity.Main DirectedHamiltonicity.Main.InputRAM DirectedHamiltonicity.Main.InputRAM.TrialParameters

theorem DirectedHamiltonicity.Main.InputRAM.TrialParameters.bootstrap_exec {τ : Tapes} {b floor cost : ℕ} (P : TrialParameters) (c d gridEnd : ℕ)
    (kernel : Cmd) (f : List Bool → ZMod 2) (u : Store)
    (beginAt : PreparedRequest P.a P.vertices P.weights P.source P.sink P.graph P.trials P.target gridEnd u)
    (width : P.fieldWidth=argumentWidth P.vertices P.weights) (dimension : P.dim=P.vertices-2)
    (baseEq : P.seenBase=seenArea P.bank P.dim c d gridEnd)
    (prefixEq : P.mask=(binaryRank P.maskLength fun i => τ.coins[i.val]?.getD false).val)
    (empty : ∀ x, P.a+68 < x → gridEnd ≤ x → u.mem x=0) (floorLow : floor ≤ P.a)
    (room : solverRoom P.bank P.dim c d gridEnd ≤ b) (hb : 2 ≤ b)
    (mw : P.maskLength+1 ≤ b) (cw : Nat.clog 2 P.card+1 ≤ b) (fit : u.Fits b)
    (query : ∀ (mode : Fin 2) (v : Store), P.header v → RequestArgs P.a 0 0 0 mode.val v → v.Fits b →
      ∃ t k, Exec τ (fun s => s.Fits b) kernel v t k ∧ k ≤ cost ∧ t.mem 0=(if mode.val=0 then P.maskLength else P.card) ∧
        t.out=v.out ∧ ∀ x ≥ floor,t.mem x=v.mem x) :
    ∃ z j, Exec τ (fun s => s.Fits b) (bootstrap P.bank c d kernel) u z j ∧
      j ≤ (d+(initSolverLayout P.bank c d).length)*(b*(5*b+9)+15)+2*cost+4*Nat.clog 2 P.card+9*P.maskLength+10 ∧
      P.invariant f ∅ z ∧ z.mem (P.a+65)=0 ∧ z.mem (P.a+68)=0 ∧ z.out=u.out := by sorry
