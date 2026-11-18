-- Prove2me | Theorems.Thm_DetANN_HPIM_PP_kids_loop
-- name    : DetANN.HPIM.PP.kids_loop
-- status  : Proved
-- author  : @milia
-- created : 2026-11-17T09:26:58.917187+00:00
-- url     : https://prove2.me/theorems/f69a6d6e-d892-41ce-a8ac-7e6b2520d699
-- title:
--   The children loop of a node
-- statement:
--   Let $B$ be blocks with `Blocks.WF`, and assume the node contract `NodeOK` at fuel $f$ (definition `DetANN_HPIMPreProg`). Let $Y$ be injective and $S$ a node with $2\le|S|\le f+2$. Assume:
--   - the run is at the start of the kids loop with index $i$ ($i+d=|S|$), the node frame (`NodeEnv`) and a frame pointer $FP$;
--   - the component labels $\mathrm{compMin}$ at $r_{\mathrm{med}}$ are in scratch;
--   - the children array is at $K_d$.
--
--   Then the run reaches NODE again, for the pending tail call on the representatives, with the invariant, the frame pointer and the scratch tops intact. Every component whose least index is $\ge i$ has a child: its sorted list, a record and the subtree $\mathrm{hpimNode}(f,C)$, all stored through the array, stably. Moreover:
--   - members of one component share one child;
--   - the heap grows by at most $\sum_C(|C|+8+\mathrm{treePts}(f,C)K_H)$ over the new components $C$, and the real heap by $\sum_C\mathrm{treePts}(f,C)K_R$;
--   - the work is at most $d\cdot\mathrm{kidW}+5+\sum_C\mathrm{treePts}(f,C)K_W$;
--   - only the array entries $\ge i$, the new heap and bounded scratch windows are written.
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

variable {m N : ℕ} (Y : Fin N → EuclideanSpace ℝ (Fin m)) (δ : ℝ) (T0 : ℕ) (v0 : ℤ)

lemma kids_loop (B : Blocks) (hB : B.WF) (KW KH KR WbI WbR f : ℕ)
    (IH : NodeOK Y δ T0 v0 B KW KH KR WbI WbR f) (hY : Function.Injective Y)
    (S : Finset (Fin N)) (hn : 2 ≤ S.card) (hnf : S.card ≤ f + 2)
    (v Sa Zn ZRn FP Kd vr : ℤ) (hHb : Hbase N T0 ≤ Sa) (hSK : Sa + S.card ≤ Kd) (hZn : Zn ≤ 0)
    (hZRn : ZRn ≤ 0) (hWb : 10 ≤ WbI) :
    ∀ d i, i + d = S.card → ∀ s : State,
      s.core.pc = B.o14 + 1 → s.halted = false → NodeEnv Y δ T0 v0 S v Sa Zn ZRn s →
      s.core.ptrs 3 = i → s.core.ptrs 19 = Kd → s.core.ptrs 21 = vr → s.core.ptrs 8 = FP →
      (∀ k : ℕ, k < S.card → s.integerMemory (Zn - 1 - k) = labOf Y S k) →
      Kd + S.card ≤ s.core.ptrs 15 → 1 + (N : ℤ) * m ≤ s.core.ptrs 16 →
      ∃ t, (run (Blocks.prog B) s detTape t).core.pc = B.lbl_NODE ∧
        (run (Blocks.prog B) s detTape t).halted = false ∧
        GInv Y δ T0 v0 (run (Blocks.prog B) s detTape t) ∧
        (run (Blocks.prog B) s detTape t).core.ptrs 2 = vr ∧
        (run (Blocks.prog B) s detTape t).core.ptrs 13 = Zn ∧
        (run (Blocks.prog B) s detTape t).core.ptrs 14 = ZRn ∧
        (run (Blocks.prog B) s detTape t).core.ptrs 8 = FP ∧
        s.core.ptrs 15 ≤ (run (Blocks.prog B) s detTape t).core.ptrs 15 ∧
        (run (Blocks.prog B) s detTape t).core.ptrs 15 ≤ s.core.ptrs 15 + kidSumH Y f S i KH ∧
        s.core.ptrs 16 ≤ (run (Blocks.prog B) s detTape t).core.ptrs 16 ∧
        (run (Blocks.prog B) s detTape t).core.ptrs 16 ≤ s.core.ptrs 16 + kidSum Y f S i * KR ∧
        (run (Blocks.prog B) s detTape t).work ≤ s.work + d * kidW S.card + 5 + kidSum Y f S i * KW ∧
        (∀ z, 0 ≤ z → z < s.core.ptrs 15 → (z < Kd + i ∨ Kd + S.card ≤ z) →
          (run (Blocks.prog B) s detTape t).integerMemory z = s.integerMemory z) ∧
        (∀ z, Zn - S.card ≤ z → z < 0 →
          (run (Blocks.prog B) s detTape t).integerMemory z = s.integerMemory z) ∧
        (∀ j (hj : j < S.card), compMin (ptsOf Y S) (dK Y S) ⟨j, hj⟩ < i →
          (run (Blocks.prog B) s detTape t).integerMemory (Kd + j) = s.integerMemory (Kd + j)) ∧
        (∀ z, 0 ≤ z → z < s.core.ptrs 16 →
          (run (Blocks.prog B) s detTape t).core.mem z = s.core.mem z) ∧
        (∀ j (hj : j < S.card), i ≤ compMin (ptsOf Y S) (dK Y S) ⟨j, hj⟩ → ∀ s'' : State,
          (∀ z, s.core.ptrs 15 ≤ z → z < (run (Blocks.prog B) s detTape t).core.ptrs 15 →
            s''.integerMemory z = (run (Blocks.prog B) s detTape t).integerMemory z) →
          (∀ z, 0 ≤ z → z < Hbase N T0 →
            s''.integerMemory z = (run (Blocks.prog B) s detTape t).integerMemory z) →
          (∀ z, s.core.ptrs 16 ≤ z → z < (run (Blocks.prog B) s detTape t).core.ptrs 16 →
            s''.core.mem z = (run (Blocks.prog B) s detTape t).core.mem z) →
          HTreeAt m s'' ((run (Blocks.prog B) s detTape t).integerMemory (Kd + j))
            (hpimNode Y δ f (compBotOf Y S ⟨j, hj⟩))) ∧
        (∀ c ∈ cellsWritten (Blocks.prog B) s t,
          (c.1 = false ∧ ((Kd + i ≤ c.2 ∧ c.2 < Kd + S.card) ∨
            (s.core.ptrs 15 ≤ c.2 ∧ c.2 < (run (Blocks.prog B) s detTape t).core.ptrs 15) ∨
            (Zn - Dn WbI S.card ≤ c.2 ∧ c.2 < Zn - S.card))) ∨
          (c.1 = true ∧ ((s.core.ptrs 16 ≤ c.2 ∧ c.2 < (run (Blocks.prog B) s detTape t).core.ptrs 16) ∨
            (ZRn - WbR ≤ c.2 ∧ c.2 < ZRn)))) := by sorry

end DetANN.HPIM.PP
