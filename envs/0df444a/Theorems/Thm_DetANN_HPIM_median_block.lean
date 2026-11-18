-- Prove2me | Theorems.Thm_DetANN_HPIM_median_block
-- name    : DetANN.HPIM.median_block
-- status  : Proved
-- author  : @milia
-- created : 2026-11-17T07:49:35.323982+00:00
-- url     : https://prove2.me/theorems/3d9ff2f9-b8fe-4b5a-b855-b873e4b586a4
-- title:
--   Median-threshold block
-- statement:
--   There are a block $\mathrm{blk}$ of fixed length $L$ (definition `DetANN_HPIMPreBlocks`) and a constant $C$ such that the following holds in every host program that embeds $\mathrm{blk}(o)$ at $o$.
--
--   Assume:
--   - $m,n\ge1$, and the local points $P_0,\dots,P_{n-1}\in\mathbb R^m$ are stored (`LocalPts`);
--   - the run starts at $pc=o$, not halted;
--   - the integer scratch top $Z$ (pointer $13$) is $\le0$.
--
--   Then the run reaches $pc=o+L$ without halting, and:
--   - real register $10$ equals the median threshold of $P$ (definition `DetANN_HPIMThreshold`);
--   - the host registers $<40$ other than real register $10$ are unchanged;
--   - it writes only integer scratch cells in $[Z-C(n+1),Z)$;
--   - its work is at most $C(n+1)^5(m+1)$.
--
--   A brute-force implementation suffices: for every candidate pair distance, count a breadth-first component.
-- source:
--   Original, written for the mission 'Deterministic Approximate Nearest Neighbors in High Dimensions' as part of a floor-free proof of DetANN.lemma_3_3 (Feng, Indyk, STOC 2027 submission, Lemma 3.3, p.7): the preprocessing program of DetANN.HPIM.hpim_preprocessing is assembled from these blocks. The machine is PNormReg (definition PNormReg_Machine) with the conventions of DetANN_DataStructure.

import Mathlib
import Definitions.Def_DetANN_HPIMPreBlocks
import Definitions.Def_DetANN_HPIMLayout

namespace DetANN.HPIM

open PNormReg PNormRegLib

/-- **Median-threshold block.** On `n` local points, it sets real register `10` to
`medThreshold pts`. It writes only integer scratch cells `[Z − C(n+1), Z)` (`Z` = pointer `13`),
and its work is at most `C (n+1)^5 (m+1)`. -/
theorem median_block :
    ∃ blk : ℕ → Program, ∃ L C : ℕ, IsBlock blk L ∧
      ∀ (off : ℕ) (Q : Program), Embeds Q (blk off) off →
      ∀ (m n : ℕ) (pts : Fin n → EuclideanSpace ℝ (Fin m)) (s : State),
        1 ≤ m → 1 ≤ n → s.core.pc = off → s.halted = false →
        LocalPts s (fun i j => pts i j) → s.core.ptrs 13 ≤ 0 →
        ∃ t, (run Q s detTape t).core.pc = off + L ∧ (run Q s detTape t).halted = false ∧
          (run Q s detTape t).core.regs 10 = medThreshold pts ∧
          KeepsLow s (run Q s detTape t) [] [10] ∧
          WritesOnly Q s t (fun c => c.1 = false ∧
            s.core.ptrs 13 - C * (n + 1) ≤ c.2 ∧ c.2 < s.core.ptrs 13) ∧
          (run Q s detTape t).work ≤ s.work + C * (n + 1) ^ 5 * (m + 1) := by sorry

end DetANN.HPIM
