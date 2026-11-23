-- Prove2me | Theorems.Thm_DetANN_RelocCall_sim_queryState
-- name    : DetANN.RelocCall.sim_queryState
-- status  : Proved
-- author  : @Mr Robbins
-- created : 2026-11-23T03:49:24.584108+00:00
-- url     : https://prove2.me/theorems/52230066-b598-44ad-bc43-1034fbb8fa9a
-- title:
--   Simulation constructor for a relocated ANN query
-- statement:
--   Let $s$ be a stored preprocessing state and let $\operatorname{queryState}(m,s,q)$ be the standard start state for a query $q\in\mathbb R^m$. A running host state $r$ simulates this virtual query state in its host-anchored frame when:
--
--   1. all renamed real registers and pointers are zero and the reserved base pointer equals $b$;
--   2. host real and integer memories equal the virtual query memories on $b+[-R,R]$;
--   3. the host cursor is zero, its work equals the frame offset $c$, and its program counter is $p.\mathrm{cOff}$.
--
--   The conclusion is
--
--   $$
--   \operatorname{Sim}\bigl(p,\operatorname{Frame.atHost}(n_R,n_Q,b,R,c,r),r,
--     \operatorname{queryState}(m,s,q)\bigr).
--   $$
--
--   Thus the virtual program counter is $0$, while the host program counter is the relocated entry. The outside-window memories are inherited from $r$ by definition and need no separate equations. This supplies the simulation hypothesis of `reloc_sim_timed_cells` for opaque query programs.
-- source:
--   Original machine-composition lemma for Feng--Indyk, Deterministic Approximate Nearest Neighbors in High Dimensions, STOC 2027 submission, §7.4, p.19; queryState is the query layout of Lemma 3.3, p.7, formalized in DetANN_DataStructure.

import Mathlib
import Definitions.Def_PNormReg_Machine
import Definitions.Def_PNormRegLib_Reloc
import Definitions.Def_PNormRegLib_Simulation
import Definitions.Def_DetANN_DataStructure
import Definitions.Def_DetANN_RelocCall

open PNormReg PNormRegLib DetANN in
/-- Start a relocated query program on the standard query layout over a stored state `s`. -/
theorem DetANN.RelocCall.sim_queryState (p : RelocParams) (nR nQ : ℕ) (b R : ℤ) (c : ℕ) (r s : State)
    (m : ℕ) (q : EuclideanSpace ℝ (Fin m))
    (hreg : ∀ i < nR, r.core.regs (p.roff + i) = 0)
    (hptr : ∀ u < nQ, r.core.ptrs (p.qoff + u) = 0)
    (hbase : r.core.ptrs p.base = b)
    (hmem : ∀ z, |z| ≤ R → r.core.mem (b + z) = (queryState m s q).core.mem z)
    (hint : ∀ z, |z| ≤ R → r.integerMemory (b + z) = (queryState m s q).integerMemory z)
    (hcursor : r.cursor = 0) (hwork : r.work = c)
    (hr : r.halted = false) (hpc : r.core.pc = p.cOff) :
    Sim p (Frame.atHost nR nQ b R c r) r (queryState m s q) := by sorry
