-- Prove2me | Theorems.Thm_DetANN_HPIM_balance_block
-- name    : DetANN.HPIM.balance_block
-- status  : Proved
-- author  : @milia
-- created : 2026-11-17T07:49:51.530327+00:00
-- url     : https://prove2.me/theorems/6a5301c9-7dd2-4cee-a27a-b6138a93911b
-- title:
--   Balance block
-- statement:
--   There are a block $\mathrm{blk}$ of fixed length $L$ (definition `DetANN_HPIMPreBlocks`) and a constant $C$ such that the following holds in every host program that embeds $\mathrm{blk}(o)$ at $o$.
--
--   Assume:
--   - $m\ge1$ (pointer $1$);
--   - a BSP $T$ is stored (`BSPAt`) from the address in pointer $17$, with integer and real windows ending at or below $0$ and starting at or above the scratch tops (pointers $13,14$);
--   - the run starts at $pc=o$, not halted;
--   - the heap pointers $H,H_R$ (pointers $15,16$) are $\ge0$.
--
--   Then the run reaches $pc=o+L$ without halting, and:
--   - it writes the box decision tree $\mathrm{balance}(T,B,[\,],\emptyset)$ (definition `DetANN_HPIMBSP`), $B=|\mathrm{paths}(T)|+1$, on the heap, with its root in pointer $17$; the stored tree depends only on the new heap cells;
--   - the host registers $<40$ other than pointers $15,16,17$ are unchanged;
--   - $H$ advances by at most $CB$ and $H_R$ by at most $CBm$;
--   - it writes only the new heap cells and scratch cells within $CB$ below the scratch tops;
--   - its work is at most $C\,B^2(m+1)$.
-- source:
--   Original, written for the mission 'Deterministic Approximate Nearest Neighbors in High Dimensions' as part of a floor-free proof of DetANN.lemma_3_3 (Feng, Indyk, STOC 2027 submission, Lemma 3.3, p.7): the preprocessing program of DetANN.HPIM.hpim_preprocessing is assembled from these blocks. The machine is PNormReg (definition PNormReg_Machine) with the conventions of DetANN_DataStructure.

import Mathlib
import Definitions.Def_DetANN_HPIMPreBlocks
import Definitions.Def_DetANN_HPIMLayout

namespace DetANN.HPIM

open PNormReg PNormRegLib

/-- **Balance block.** From a BSP `T` stored in scratch (its windows above the scratch tops and
`≤ 0`), it writes the box decision tree `balance T (T.paths.card + 1) [] ∅` on the heap and returns
its root in pointer `17`. The stored tree depends only on the new heap cells. The heap pointers (`15`, `16`, both `≥ 0`) advance by at most `C B` and
`C B m`, where `B = T.paths.card + 1`. It writes only the new heap cells and scratch cells within
`C B` below the scratch tops, and its work is at most `C B² (m+1)`. -/
theorem balance_block :
    ∃ blk : ℕ → Program, ∃ L C : ℕ, IsBlock blk L ∧
      ∀ (off : ℕ) (Q : Program), Embeds Q (blk off) off →
      ∀ (m : ℕ) (T : BSP m) (s : State) (ilo ihi rlo rhi : ℤ),
        1 ≤ m → s.core.pc = off → s.halted = false → s.core.ptrs 1 = m →
        BSPAt m s ilo ihi rlo rhi (s.core.ptrs 17) T → ihi ≤ 0 → rhi ≤ 0 →
        s.core.ptrs 13 ≤ ilo → s.core.ptrs 14 ≤ rlo → 0 ≤ s.core.ptrs 15 → 0 ≤ s.core.ptrs 16 →
        ∃ t, (run Q s detTape t).core.pc = off + L ∧ (run Q s detTape t).halted = false ∧
          (∀ s'' : State,
            (∀ z, s.core.ptrs 15 ≤ z → z < (run Q s detTape t).core.ptrs 15 →
              s''.integerMemory z = (run Q s detTape t).integerMemory z) →
            (∀ z, s.core.ptrs 16 ≤ z → z < (run Q s detTape t).core.ptrs 16 →
              s''.core.mem z = (run Q s detTape t).core.mem z) →
            BoxTreeAt m s'' ((run Q s detTape t).core.ptrs 17) (balance T (T.paths.card + 1) [] ∅)) ∧
          KeepsLow s (run Q s detTape t) [15, 16, 17] [] ∧
          s.core.ptrs 15 ≤ (run Q s detTape t).core.ptrs 15 ∧
          (run Q s detTape t).core.ptrs 15 ≤ s.core.ptrs 15 + C * (T.paths.card + 1) ∧
          s.core.ptrs 16 ≤ (run Q s detTape t).core.ptrs 16 ∧
          (run Q s detTape t).core.ptrs 16 ≤ s.core.ptrs 16 + C * (T.paths.card + 1) * m ∧
          WritesOnly Q s t (fun c =>
            ((if c.1 then s.core.ptrs 14 else s.core.ptrs 13) - C * (T.paths.card + 1) ≤ c.2 ∧
              c.2 < (if c.1 then s.core.ptrs 14 else s.core.ptrs 13)) ∨
            ((if c.1 then s.core.ptrs 16 else s.core.ptrs 15) ≤ c.2 ∧
              c.2 < (if c.1 then (run Q s detTape t).core.ptrs 16
                else (run Q s detTape t).core.ptrs 15))) ∧
          (run Q s detTape t).work ≤ s.work + C * (T.paths.card + 1) ^ 2 * (m + 1) := by sorry

end DetANN.HPIM
