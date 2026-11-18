-- Prove2me | Theorems.Thm_DetANN_HPIM_build_block
-- name    : DetANN.HPIM.build_block
-- status  : Proved
-- author  : @milia
-- created : 2026-11-17T07:50:07.721651+00:00
-- url     : https://prove2.me/theorems/f115f535-18b9-433d-8fc2-60ad24ed091f
-- title:
--   BSP block
-- statement:
--   There are a block $\mathrm{blk}$ of fixed length $L$ (definition `DetANN_HPIMPreBlocks`) and a constant $C$ such that the following holds in every host program that embeds $\mathrm{blk}(o)$ at $o$.
--
--   Assume:
--   - $m,n\ge1$, and the local points $P_0,\dots,P_{n-1}\in\mathbb R^m$ are stored (`LocalPts`);
--   - real registers $11,12$ hold a radius $r$ and a factor $c$;
--   - a box $[lo,hi]$ is stored at the real address in pointer $17$, which is $\ge0$;
--   - the scratch tops $Z,Z_R$ (pointers $13,14$) are $\le0$;
--   - the recursion of `build` (definition `DetANN_HPIMBuild`) does not starve with fuel $f$.
--
--   Then the run reaches $pc=o+L$ without halting, and:
--   - it stores the BSP $T=\mathrm{build}(P,r,c,f,lo,hi)$ in scratch (`BSPAt`), with its root in pointer $17$;
--   - the new tops $Z',Z_R'$ lie below the stored tree and at most $C\,B\,(m+1)$ below the old tops, where $B=|\mathrm{paths}(T)|+1$;
--   - the host registers $<40$ other than pointers $13,14,17$ are unchanged;
--   - it writes only scratch cells in those windows;
--   - its work is at most $C\,B^2(n+1)(m+1)^2$.
-- source:
--   Original, written for the mission 'Deterministic Approximate Nearest Neighbors in High Dimensions' as part of a floor-free proof of DetANN.lemma_3_3 (Feng, Indyk, STOC 2027 submission, Lemma 3.3, p.7): the preprocessing program of DetANN.HPIM.hpim_preprocessing is assembled from these blocks. The machine is PNormReg (definition PNormReg_Machine) with the conventions of DetANN_DataStructure.

import Mathlib
import Definitions.Def_DetANN_HPIMPreBlocks
import Definitions.Def_DetANN_HPIMLayout

namespace DetANN.HPIM

open PNormReg PNormRegLib

/-- **BSP block.** On `n` local points, a radius `r` and a factor `c` (real registers `11`, `12`), and
a box `[lo, hi]` stored at real address `p17 ≥ 0`, when `build` does not starve with fuel `f`, it
stores `build pts r c f lo hi` in scratch and returns its root in pointer `17`. The new scratch tops
`Z'`, `ZR'` (pointers `13`, `14`) lie below the stored tree. With `B = paths.card + 1`, it writes only
scratch cells within `C B (m+1)` below the old tops, and its work is at most
`C B² (n+1) (m+1)²`. -/
theorem build_block :
    ∃ blk : ℕ → Program, ∃ L C : ℕ, IsBlock blk L ∧
      ∀ (off : ℕ) (Q : Program), Embeds Q (blk off) off →
      ∀ (m n f : ℕ) (pts : Fin n → Fin m → ℝ) (r c : ℝ) (lo hi : Fin m → ℝ) (s : State),
        1 ≤ m → 1 ≤ n → s.core.pc = off → s.halted = false → LocalPts s pts →
        s.core.regs 11 = r → s.core.regs 12 = c → 0 ≤ s.core.ptrs 17 →
        (∀ j : Fin m, s.core.mem (s.core.ptrs 17 + j) = lo j) →
        (∀ j : Fin m, s.core.mem (s.core.ptrs 17 + m + j) = hi j) →
        s.core.ptrs 13 ≤ 0 → s.core.ptrs 14 ≤ 0 → ¬ Starves pts r c f lo hi →
        ∃ t, (run Q s detTape t).core.pc = off + L ∧ (run Q s detTape t).halted = false ∧
          BSPAt m (run Q s detTape t) ((run Q s detTape t).core.ptrs 13) (s.core.ptrs 13)
            ((run Q s detTape t).core.ptrs 14) (s.core.ptrs 14) ((run Q s detTape t).core.ptrs 17)
            (build pts r c f lo hi) ∧
          KeepsLow s (run Q s detTape t) [13, 14, 17] [] ∧
          s.core.ptrs 13 - C * ((build pts r c f lo hi).paths.card + 1) * (m + 1) ≤
            (run Q s detTape t).core.ptrs 13 ∧
          s.core.ptrs 14 - C * ((build pts r c f lo hi).paths.card + 1) * (m + 1) ≤
            (run Q s detTape t).core.ptrs 14 ∧
          WritesOnly Q s t (fun w =>
            (if w.1 then s.core.ptrs 14 else s.core.ptrs 13) -
                C * ((build pts r c f lo hi).paths.card + 1) * (m + 1) ≤ w.2 ∧
              w.2 < (if w.1 then s.core.ptrs 14 else s.core.ptrs 13)) ∧
          (run Q s detTape t).work ≤ s.work +
            C * ((build pts r c f lo hi).paths.card + 1) ^ 2 * (n + 1) * (m + 1) ^ 2 := by sorry

end DetANN.HPIM
