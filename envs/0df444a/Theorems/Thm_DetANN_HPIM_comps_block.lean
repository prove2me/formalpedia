-- Prove2me | Theorems.Thm_DetANN_HPIM_comps_block
-- name    : DetANN.HPIM.comps_block
-- status  : Proved
-- author  : @milia
-- created : 2026-11-17T07:49:38.290625+00:00
-- url     : https://prove2.me/theorems/991e6faa-6ada-43db-9e1c-6d9d6ad8244f
-- title:
--   Components block
-- statement:
--   There are a block $\mathrm{blk}$ of fixed length $L$ (definition `DetANN_HPIMPreBlocks`) and a constant $C$ such that the following holds in every host program that embeds $\mathrm{blk}(o)$ at $o$.
--
--   Assume:
--   - $m,n\ge1$, and the local points $P_0,\dots,P_{n-1}\in\mathbb R^m$ are stored (`LocalPts`);
--   - real register $10$ holds a threshold $d\ge0$;
--   - the run starts at $pc=o$, not halted;
--   - the integer scratch top $Z$ (pointer $13$) is $\le0$.
--
--   Then the run reaches $pc=o+L$ without halting, and:
--   - for every $i<n$, integer cell $Z-1-i$ holds $\mathrm{compMin}(P,d,i)$, the least index in the component of $i$ in the threshold graph at $d$;
--   - all host registers $<40$ are unchanged;
--   - it writes only integer scratch cells in $[Z-C(n+1),Z)$;
--   - its work is at most $C(n+1)^3(m+1)$.
-- source:
--   Original, written for the mission 'Deterministic Approximate Nearest Neighbors in High Dimensions' as part of a floor-free proof of DetANN.lemma_3_3 (Feng, Indyk, STOC 2027 submission, Lemma 3.3, p.7): the preprocessing program of DetANN.HPIM.hpim_preprocessing is assembled from these blocks. The machine is PNormReg (definition PNormReg_Machine) with the conventions of DetANN_DataStructure.

import Mathlib
import Definitions.Def_DetANN_HPIMPreBlocks
import Definitions.Def_DetANN_HPIMLayout

namespace DetANN.HPIM

open PNormReg PNormRegLib

/-- **Components block.** On `n` local points and a threshold `d ≥ 0` (real register `10`), it
writes `compMin pts d i` to integer cell `Z − 1 − i` for every `i < n` (`Z` = pointer `13`). It
writes only integer scratch cells `[Z − C(n+1), Z)`, and its work is at most `C (n+1)^3 (m+1)`. -/
theorem comps_block :
    ∃ blk : ℕ → Program, ∃ L C : ℕ, IsBlock blk L ∧
      ∀ (off : ℕ) (Q : Program), Embeds Q (blk off) off →
      ∀ (m n : ℕ) (pts : Fin n → EuclideanSpace ℝ (Fin m)) (d : ℝ) (s : State),
        1 ≤ m → 1 ≤ n → s.core.pc = off → s.halted = false →
        LocalPts s (fun i j => pts i j) → s.core.regs 10 = d → 0 ≤ d → s.core.ptrs 13 ≤ 0 →
        ∃ t, (run Q s detTape t).core.pc = off + L ∧ (run Q s detTape t).halted = false ∧
          (∀ i : Fin n, (run Q s detTape t).integerMemory (s.core.ptrs 13 - 1 - i) = compMin pts d i) ∧
          KeepsLow s (run Q s detTape t) [] [] ∧
          WritesOnly Q s t (fun c => c.1 = false ∧
            s.core.ptrs 13 - C * (n + 1) ≤ c.2 ∧ c.2 < s.core.ptrs 13) ∧
          (run Q s detTape t).work ≤ s.work + C * (n + 1) ^ 3 * (m + 1) := by sorry

end DetANN.HPIM
