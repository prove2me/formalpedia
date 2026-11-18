-- Prove2me | Theorems.Thm_DetANN_HPIM_PP_init_spec
-- name    : DetANN.HPIM.PP.init_spec
-- status  : Proved
-- author  : @milia
-- created : 2026-11-17T09:27:08.195944+00:00
-- url     : https://prove2.me/theorems/8a631226-e1eb-4339-8cf6-e2183e110cdb
-- title:
--   Initialization of the preprocessing run
-- statement:
--   Let $B$ be blocks with `Blocks.WF`, $N\ge1$ and $\delta>0$. From the input state of $Y_1,\dots,Y_N\in\mathbb R^m$ (definition `DetANN_DataStructure`), the program $\mathrm{prog}(B)$ (definition `DetANN_HPIMPreProg`) reaches NODE without halting, with:
--   - the global invariant `GInv` for $T_{0G}$ and the root record $v_{0G}$;
--   - the root list of all indices at $H_{\mathrm{base}}$, with $I[v_{0G}+3]=H_{\mathrm{base}}$ and $I[v_{0G}+7]=N$;
--   - the frame pointer and scratch tops at $-10$, $0$ and $-10$, with $I[-10]=0$ (halt code);
--   - the heap tops at $v_{0G}+8$ and $1+Nm$.
--
--   Its work is at most $75+4\lceil\log_2N\rceil+11N+5K_G+10T_{0G}$, and it writes only integer cells in $[-10,v_{0G}+8)$.
-- source:
--   Original, written for the mission 'Deterministic Approximate Nearest Neighbors in High Dimensions' as part of a floor-free proof of DetANN.lemma_3_3 (Feng, Indyk, STOC 2027 submission, Lemma 3.3, p.7). These are the intermediate steps of the reduction of DetANN.HPIM.hpim_preprocessing, split so that each proof fits the verifier's time limit. The machine is PNormReg (definition PNormReg_Machine) with the conventions of DetANN_DataStructure.

import Mathlib
import Definitions.Def_DetANN_HPIMPreProg
import Definitions.Def_PNormReg_Machine
import Definitions.Def_PNormRegLib_Exec
import Definitions.Def_DetANN_DataStructure
import Definitions.Def_DetANN_HPIMLayout
import Definitions.Def_DetANN_HPIMWF
import Definitions.Def_PNormRegLib_Reloc
import Definitions.Def_DetANN_HPIMPreBlocks

namespace DetANN.HPIM.PP

open PNormReg PNormRegLib SmaleNinth DetANN DetANN.HPIM Classical

variable {m N : ℕ} (Y : Fin N → EuclideanSpace ℝ (Fin m)) (δ : ℝ)

/-- **Initialization**: from the input layout to `NODE` on the root. -/
theorem init_spec (B : Blocks) (hB : B.WF) (hN : 1 ≤ N) (hδ : 0 < δ) :
    ∃ t, (run (Blocks.prog B) (inputState Y δ) detTape t).core.pc = B.lbl_NODE ∧
      (run (Blocks.prog B) (inputState Y δ) detTape t).halted = false ∧
      GInv Y δ (T0G N δ) (v0G N δ) (run (Blocks.prog B) (inputState Y δ) detTape t) ∧
      (run (Blocks.prog B) (inputState Y δ) detTape t).core.ptrs 2 = v0G N δ ∧
      (run (Blocks.prog B) (inputState Y δ) detTape t).core.ptrs 13 = -10 ∧
      (run (Blocks.prog B) (inputState Y δ) detTape t).core.ptrs 14 = 0 ∧
      (run (Blocks.prog B) (inputState Y δ) detTape t).core.ptrs 8 = -10 ∧
      (run (Blocks.prog B) (inputState Y δ) detTape t).core.ptrs 15 = v0G N δ + 8 ∧
      (run (Blocks.prog B) (inputState Y δ) detTape t).core.ptrs 16 = 1 + (N : ℤ) * m ∧
      (run (Blocks.prog B) (inputState Y δ) detTape t).integerMemory (v0G N δ + 3) =
        Hbase N (T0G N δ) ∧
      (run (Blocks.prog B) (inputState Y δ) detTape t).integerMemory (v0G N δ + 7) = N ∧
      SList (run (Blocks.prog B) (inputState Y δ) detTape t) (Hbase N (T0G N δ))
        (Finset.univ : Finset (Fin N)) ∧
      (run (Blocks.prog B) (inputState Y δ) detTape t).integerMemory (-10) = 0 ∧
      (run (Blocks.prog B) (inputState Y δ) detTape t).work ≤
        75 + 4 * Nat.clog 2 N + 11 * N + 5 * KG N δ + 10 * T0G N δ ∧
      (∀ c ∈ cellsWritten (Blocks.prog B) (inputState Y δ) t,
        c.1 = false ∧ -10 ≤ c.2 ∧ c.2 < v0G N δ + 8) := by sorry

end DetANN.HPIM.PP
