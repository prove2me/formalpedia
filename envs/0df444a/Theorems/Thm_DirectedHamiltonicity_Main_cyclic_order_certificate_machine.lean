-- Prove2me | Theorems.Thm_DirectedHamiltonicity_Main_cyclic_order_certificate_machine
-- name    : DirectedHamiltonicity.Main.cyclic_order_certificate_machine
-- status  : Proved
-- author  : @Soh Kumabe
-- created : 2026-11-26T15:28:06.581446+00:00
-- url     : https://prove2.me/theorems/1838a611-31f9-5353-b79a-01ec86978346
-- title:
--   Theorem 1: a fixed log-cost RAM verifier for a proposed cyclic order
-- statement:
--   On the registered directed graph tape a single RAM fragment checks two candidate arrays: a cyclic order with a final return vertex, and a claimed inverse. For every typed assignment it accepts exactly when the order is closed, each directed arc is present, and the inverse is a left inverse at every position. Such an assignment exists exactly on a Hamiltonian input. The statement gives the finite machine trace and its cost. The candidate arrays are supplied in memory.
-- source:
--   T. Koana and S. Kumabe, Breaking the 2^n barrier for directed hamiltonicity, STOC 2027 submission #811. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/811.pdf Witness-checking step in the proof of Theorem 1.

import Mathlib
import Definitions.Def_DirectedHamiltonicity_Main_Graphs
import Definitions.Def_DirectedHamiltonicity_Main_Algorithms

open TargetedSamplers DirectedHamiltonicity.Main

open Classical in
theorem DirectedHamiltonicity.Main.cyclic_order_certificate_machine :
    ∃ P : Program, ∀ (n : ℕ) (adj : Fin n → Fin n → Bool),
      let valid := fun (q : Fin (n+1) → Fin n) (inv : Fin n → Fin n) =>
        q 0 = q (Fin.last n) ∧ ∀ i : Fin n, adj (q i.castSucc) (q i.succ) = true ∧ inv (q i.castSucc) = i
      (HasHamCycle n adj ↔ ∃ q inv, valid q inv) ∧
      ∀ q inv (τ : Tapes) (s : State), τ.input=encodeDigraph n adj → s.pc=0 → s.halted=false →
        s.mem 20=32 → s.mem 21=33+n → s.mem 22=n →
        (∀ i : Fin (n+1), s.mem (32+i.val) = (q i).val) →
        (∀ i : Fin n, s.mem (33+n+i.val) = (inv i).val) →
        ∃ k z, (P.step τ)^[k] s=z ∧ z.pc=P.length ∧ z.halted=false ∧
          z.out=s.out ∧ z.bot=s.bot ∧ (z.mem 23=1 ↔ valid q inv) ∧
          (z.mem 23=1 → HasHamCycle n adj) ∧ z.work ≤ s.work +
            (n+2)*(300*(11+(130+2*n).size)+(n.size+1)*(8000+2000*(n.size+10))) := by sorry
