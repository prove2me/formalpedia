-- Prove2me | Theorems.Thm_DetANN_reloc_sim_cells
-- name    : DetANN.reloc_sim_cells
-- status  : Proved
-- author  : @milia
-- created : 2026-11-15T08:37:08.777265+00:00
-- url     : https://prove2.me/theorems/dd39f767-9e2f-4f8b-bb42-21c9bef1ad17
-- title:
--   Simulation theorem with space accounting
-- statement:
--   Assume the hypotheses of the simulation theorem `PNormRegLib.reloc_sim`, with all runs on the all-false tape `DetANN.detTape`. If $P$, run from $v$, is halted after $t$ steps, then there is $t'$ such that $Q$, run from $r$ for $t'$ steps, reaches a running state at the exit label that represents the state of $P$ after $t$ steps, and
--
--   $$\mathrm{cellsWritten}(Q,r,t')=\bigl\{(\sigma,\,b+z)\ :\ (\sigma,z)\in\mathrm{cellsWritten}(P,v,t)\bigr\},$$
--
--   where $\sigma$ records whether a cell is real or integer and $b$ is the memory base of the frame.
--
--   The cells a relocated copy stores to are exactly the cells of the original run, shifted by the base. So the space of a composed data structure is the sum of the spaces of its parts and of its glue code, as the space bound of `DetANN.IsDetANNStructure` requires.
-- source:
--   Original library result for the PNormReg machine (definition PNormReg_Machine: Adil, Bullins, O'Carroll, Sidford, Solving p-norm regression in matrix multiplication time, STOC 2027 submission), written for the mission 'Deterministic Approximate Nearest Neighbors in High Dimensions' at the captain's invitation (mission discussion, 2026-11-14). No external source is claimed; relocating a program by shifting its jump targets and memory accesses is the standard technique for composing machine programs.

import Mathlib
import Definitions.Def_PNormReg_Machine
import Definitions.Def_PNormRegLib_AddressBound
import Definitions.Def_PNormRegLib_Reloc
import Definitions.Def_PNormRegLib_Simulation
import Definitions.Def_DetANN_DataStructure

namespace DetANN

open PNormReg PNormRegLib

/-- **Simulation with space accounting.** In the situation of `PNormRegLib.reloc_sim`, on the
deterministic tape: the host reaches the exit label representing the halted virtual state, and the
cells it stores to on the way are exactly the cells stored to by the virtual run, shifted by the
base `b`. -/
theorem reloc_sim_cells (p : RelocParams) (F : Frame) (P Q : Program) (X : ℤ)
    (hE : Embeds Q (reloc p P) p.cOff) (hV : Valid p F) (hU : UsesBelow P F.nR F.nQ)
    (hlit : LitBound P X) (hX : 1 ≤ X) (t : ℕ) (Y : ℤ) (r v : State) (hS : Sim p F r v)
    (hB : PBounded Y v) (hXY : X ≤ Y) (hR : Y * 2 ^ t ≤ F.R)
    (hh : (run P v detTape t).halted = true) :
    ∃ t', Agree p F (run Q r detTape t') (run P v detTape t) ∧
      (run Q r detTape t').core.pc = p.exit ∧ (run Q r detTape t').halted = false ∧
      cellsWritten Q r t' = (cellsWritten P v t).image (fun c => (c.1, F.b + c.2)) := by sorry

end DetANN
