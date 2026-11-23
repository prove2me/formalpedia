-- Prove2me | Theorems.Thm_DetANN_RelocCall_sim_inputState
-- name    : DetANN.RelocCall.sim_inputState
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:48:03.315671+00:00
-- url     : https://prove2.me/theorems/0a847eff-11ef-4eef-b6b5-8c84fdc9051c
-- title:
--   Simulation constructor for a relocated preprocessing input
-- statement:
--   Let $Y:[N]\to\mathbb R^m$ and $\theta\in\mathbb R$ determine the standard ANN preprocessing input state, and let $r$ be a running host state. If the renamed real registers and pointer registers of $r$ are zero, its reserved base pointer is $b$, its real and integer memories agree with the input layout throughout the window $b+[-R,R]$, its cursor is zero, its work is $c$, and its program counter is the relocation entry offset, then
--
--   $$
--   \operatorname{Sim}\bigl(p,\operatorname{Frame.atHost}(n_R,n_Q,b,R,c,r),r,
--     \operatorname{inputState}(Y,\theta)\bigr).
--   $$
--
--   In particular, the virtual program counter is $0$ and the host program counter is exactly $p.\mathrm{cOff}$. Memories outside the window require no hypotheses because the frame is anchored at $r$. This is the direct entry adapter for calling an opaque preprocessing program with `reloc_sim_timed_cells`.
-- source:
--   Original machine-composition lemma for Feng--Indyk, Deterministic Approximate Nearest Neighbors in High Dimensions, STOC 2027 submission, §7.4, p.19; inputState is the layout of Lemma 3.3, p.7, formalized in DetANN_DataStructure.

import Mathlib
import Definitions.Def_PNormReg_Machine
import Definitions.Def_PNormRegLib_Reloc
import Definitions.Def_PNormRegLib_Simulation
import Definitions.Def_DetANN_DataStructure
import Definitions.Def_DetANN_RelocCall

open PNormReg PNormRegLib DetANN in
/-- Start a relocated program on the standard preprocessing input layout from explicit host
register, base, window-memory, counter, running and program-counter equations. -/
theorem DetANN.RelocCall.sim_inputState (p : RelocParams) (nR nQ : ℕ) (b R : ℤ) (c : ℕ) (r : State)
    {N m : ℕ} (Y : Fin N → EuclideanSpace ℝ (Fin m)) (θ : ℝ)
    (hreg : ∀ i < nR, r.core.regs (p.roff + i) = 0)
    (hptr : ∀ q < nQ, r.core.ptrs (p.qoff + q) = 0)
    (hbase : r.core.ptrs p.base = b)
    (hmem : ∀ z, |z| ≤ R → r.core.mem (b + z) = (inputState Y θ).core.mem z)
    (hint : ∀ z, |z| ≤ R → r.integerMemory (b + z) = (inputState Y θ).integerMemory z)
    (hcursor : r.cursor = 0) (hwork : r.work = c)
    (hr : r.halted = false) (hpc : r.core.pc = p.cOff) :
    Sim p (Frame.atHost nR nQ b R c r) r (inputState Y θ) := by sorry
