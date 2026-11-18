-- Prove2me | Theorems.Thm_DetANN_HPIM_BD_peel_specs
-- name    : DetANN.HPIM.BD.peel_specs
-- status  : Proved
-- author  : @milia
-- created : 2026-11-17T21:34:22.856612+00:00
-- url     : https://prove2.me/theorems/17caa0e3-f72e-4f48-a6f5-8990a3242079
-- title:
--   Composite parts of the BSP construction block: the split and the two peels
-- statement:
--   Three composite facts about the program $\mathrm{bd}$ of definition `DetANN_HPIMBuildProg`, stated with `Env`, `BoxAt` and `Fr` from the same definition. In each, $Q$ contains $\mathrm{bd}(o)$ at offset $o$, $s$ is not halted, `Env s pts r c Z0` holds and $1\le m$. $Z$, $R$ are pointers 13, 14 of $s$.
--
--   1. **Split** (from 197, when $\neg(2\sigma_{51}-\sigma_{52}\le0)$, real 52 holds $\sigma(lo,hi)$ of the task box at pointer 43, $Z\le p_{44}$ and $R\le p_{43}$). Some $t\le37m+91$ and $k$ with $\mathrm{longestAxis}(lo,hi)=k$ bring the run to 34 (not halted). With $\mu=(lo_k+hi_k)/2$:
--      - there is a cut node $[1,p_{43}]$ at $Z-4$, with $I[p_{44}]=Z-4$;
--      - the left half $(lo,hi[k\mapsto\mu])$ is stored at $R-2m$ and the right half $(lo[k\mapsto\mu],hi)$ at $R-4m$;
--      - the entries $[R-2m,Z-2,p_{42}]$ at $Z-7$ and $[R-4m,Z-1,Z-7]$ at $Z-10$ are pushed, with pointers $13,42:=Z-10$ and $14:=R-4m$;
--      - the constant registers, pointers below 13 and between 14 and 42, 59, 60, 68, 69, and reals below 44 and 49, 50, 53 are kept;
--      - real cells outside $[R-4m,R)$ and integer cells outside $[Z-10,Z)\cup\{p_{44}\}$ are kept, and the writes stay in these windows.
--   2. **Low peel** (from 283 with axis $k<m$, the current box $[lo,hi]$ at pointer 54 and the core $[tlo,thi]$ at pointer 48, when $lo_k<tlo_k$; the current slot $p_{55}$ satisfies $Z\le p_{55}<0$, and $p_{54},p_{48}\ge R$, $Z\le0$, $R\le0$). Some $t\le28m+80$ gives $\mathrm{Fr}\,Q\,s\,s'\,t\,\{p_{55}\}$, the pc 326, `Env` for $s'$, and:
--      - pointers $13,42:=Z-7$, $14:=R-4m$, $54:=R-4m$, $55:=Z-1$, with 48 and 53 kept;
--      - a cut node $[1,p_{54}]$ at $Z-4$, with $I[p_{55}]=Z-4$;
--      - the entry $[R-2m,Z-2,p_{42}]$ at $Z-7$;
--      - the low slab $(lo,hi[k\mapsto tlo_k])$ at $R-2m$ and the rest $(lo[k\mapsto tlo_k],hi)$ at $R-4m$.
--   3. **High peel** (from 326, when $hi_k>thi_k$; same hypotheses). The same as 2, except that the pc is 283, the axis is $k+1$, the current slot is $Z-2$, the entry is $[R-2m,Z-1,p_{42}]$, the high slab $(lo[k\mapsto thi_k],hi)$ is at $R-2m$ and the rest $(lo,hi[k\mapsto thi_k])$ is at $R-4m$.
-- source:
--   Original, written for the mission 'Deterministic Approximate Nearest Neighbors in High Dimensions' as part of a floor-free proof of DetANN.lemma_3_3 (Feng, Indyk, STOC 2027 submission, Lemma 3.3, p.7). These are pieces of the BSP construction block of DetANN.HPIM.build_block, split out so that each proof fits the verifier's time limit. The machine is PNormReg (definition PNormReg_Machine) with the conventions of DetANN_DataStructure.

import Mathlib
import Definitions.Def_DetANN_HPIMBuildProg
import Definitions.Def_PNormReg_Machine
import Definitions.Def_PNormRegLib_Exec
import Definitions.Def_DetANN_DataStructure
import Definitions.Def_PNormRegLib_Reloc
import Definitions.Def_DetANN_HPIMBuild
import Definitions.Def_DetANN_HPIMPreBlocks

namespace DetANN.HPIM.BD

open PNormReg PNormRegLib DetANN DetANN.HPIM

theorem peel_specs :
    (∀ {m n : ℕ} (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (pts : Fin n → Fin m → ℝ) (r c : ℝ) (Z0 : ℤ) (hm : 1 ≤ m) (lo hi : Fin m → ℝ) (s : State) (hpc : s.core.pc = off + 197) (hh : s.halted = false) (hEnv : Env s pts r c Z0) (h52 : s.core.regs 52 = sigma lo hi) (hc : ¬ (s.core.regs 51 + s.core.regs 51 - s.core.regs 52 ≤ 0)) (hB : BoxAt s (s.core.ptrs 43) lo hi) (hsl : s.core.ptrs 13 ≤ s.core.ptrs 44) (hp : s.core.ptrs 14 ≤ s.core.ptrs 43),
      ∃ (t : ℕ) (s' : State) (k : Fin m), run Q s detTape t = s' ∧ t ≤ 37 * m + 91 ∧ longestAxis lo hi = some k ∧ s'.core.pc = off + 34 ∧ s'.halted = false ∧ s'.core.ptrs 13 = s.core.ptrs 13 - 10 ∧ s'.core.ptrs 14 = s.core.ptrs 14 - 4 * m ∧ s'.core.ptrs 42 = s.core.ptrs 13 - 10 ∧ s'.integerMemory (s.core.ptrs 13 - 4) = 1 ∧ s'.integerMemory (s.core.ptrs 13 - 3) = s.core.ptrs 43 ∧ s'.integerMemory (s.core.ptrs 44) = s.core.ptrs 13 - 4 ∧ s'.integerMemory (s.core.ptrs 13 - 7) = s.core.ptrs 14 - 2 * m ∧ s'.integerMemory (s.core.ptrs 13 - 6) = s.core.ptrs 13 - 2 ∧ s'.integerMemory (s.core.ptrs 13 - 5) = s.core.ptrs 42 ∧ s'.integerMemory (s.core.ptrs 13 - 10) = s.core.ptrs 14 - 4 * m ∧ s'.integerMemory (s.core.ptrs 13 - 9) = s.core.ptrs 13 - 1 ∧ s'.integerMemory (s.core.ptrs 13 - 8) = s.core.ptrs 13 - 7 ∧ BoxAt s' (s.core.ptrs 14 - 2 * m) lo (setCoord hi k ((lo k + hi k) / 2)) ∧ BoxAt s' (s.core.ptrs 14 - 4 * m) (setCoord lo k ((lo k + hi k) / 2)) hi ∧ (∀ x, (x < 13 ∨ (14 < x ∧ x < 42) ∨ x = 40 ∨ x = 59 ∨ x = 60 ∨ x = 68 ∨ x = 69) → s'.core.ptrs x = s.core.ptrs x) ∧ (∀ x, (x < 44 ∨ x = 49 ∨ x = 50 ∨ x = 53) → s'.core.regs x = s.core.regs x) ∧ (∀ z, (z < s.core.ptrs 14 - 4 * m ∨ s.core.ptrs 14 ≤ z) → s'.core.mem z = s.core.mem z) ∧ (∀ z, (z < s.core.ptrs 13 - 10 ∨ s.core.ptrs 13 ≤ z) → z ≠ s.core.ptrs 44 → s'.integerMemory z = s.integerMemory z) ∧ s'.work = s.work + t ∧ (∀ w ∈ cellsWritten Q s t, (w.1 = false ∧ ((s.core.ptrs 13 - 10 ≤ w.2 ∧ w.2 < s.core.ptrs 13) ∨ w.2 = s.core.ptrs 44)) ∨ (w.1 = true ∧ s.core.ptrs 14 - 4 * m ≤ w.2 ∧ w.2 < s.core.ptrs 14))) ∧
    (∀ {m n : ℕ} (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (pts : Fin n → Fin m → ℝ) (r c : ℝ) (Z0 : ℤ) (hm : 1 ≤ m) (s : State) (hpc : s.core.pc = off + 283) (hh : s.halted = false) (hEnv : Env s pts r c Z0) (k : ℕ) (hk : k < m) (h53 : s.core.ptrs 53 = k) (tlo thi lo hi : Fin m → ℝ) (hQ : BoxAt s (s.core.ptrs 48) tlo thi) (hB : BoxAt s (s.core.ptrs 54) lo hi) (hlow : lo ⟨k, hk⟩ < tlo ⟨k, hk⟩) (hcsl : s.core.ptrs 13 ≤ s.core.ptrs 55) (hcb : s.core.ptrs 14 ≤ s.core.ptrs 54) (hq : s.core.ptrs 14 ≤ s.core.ptrs 48) (hZ : s.core.ptrs 13 ≤ 0) (hcsl0 : s.core.ptrs 55 < 0) (hR : s.core.ptrs 14 ≤ 0),
      ∃ (t : ℕ) (s' : State), Fr Q s s' t (fun z => z = s.core.ptrs 55) ∧ t ≤ 28 * m + 80 ∧ s'.core.pc = off + 326 ∧ s'.halted = false ∧ Env s' pts r c Z0 ∧ s'.core.ptrs 13 = s.core.ptrs 13 - 7 ∧ s'.core.ptrs 14 = s.core.ptrs 14 - 4 * m ∧ s'.core.ptrs 42 = s.core.ptrs 13 - 7 ∧ s'.core.ptrs 48 = s.core.ptrs 48 ∧ s'.core.ptrs 53 = k ∧ s'.core.ptrs 54 = s.core.ptrs 14 - 4 * m ∧ s'.core.ptrs 55 = s.core.ptrs 13 - 1 ∧ s'.integerMemory (s.core.ptrs 13 - 4) = 1 ∧ s'.integerMemory (s.core.ptrs 13 - 3) = s.core.ptrs 54 ∧ s'.integerMemory (s.core.ptrs 55) = s.core.ptrs 13 - 4 ∧ s'.integerMemory (s.core.ptrs 13 - 7) = s.core.ptrs 14 - 2 * m ∧ s'.integerMemory (s.core.ptrs 13 - 6) = s.core.ptrs 13 - 2 ∧ s'.integerMemory (s.core.ptrs 13 - 5) = s.core.ptrs 42 ∧ BoxAt s' (s.core.ptrs 14 - 2 * m) lo (setCoord hi k (tlo ⟨k, hk⟩)) ∧ BoxAt s' (s.core.ptrs 14 - 4 * m) (setCoord lo k (tlo ⟨k, hk⟩)) hi) ∧
    (∀ {m n : ℕ} (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (pts : Fin n → Fin m → ℝ) (r c : ℝ) (Z0 : ℤ) (hm : 1 ≤ m) (s : State) (hpc : s.core.pc = off + 326) (hh : s.halted = false) (hEnv : Env s pts r c Z0) (k : ℕ) (hk : k < m) (h53 : s.core.ptrs 53 = k) (tlo thi lo hi : Fin m → ℝ) (hQ : BoxAt s (s.core.ptrs 48) tlo thi) (hB : BoxAt s (s.core.ptrs 54) lo hi) (hhigh : hi ⟨k, hk⟩ > thi ⟨k, hk⟩) (hcsl : s.core.ptrs 13 ≤ s.core.ptrs 55) (hcb : s.core.ptrs 14 ≤ s.core.ptrs 54) (hq : s.core.ptrs 14 ≤ s.core.ptrs 48) (hZ : s.core.ptrs 13 ≤ 0) (hcsl0 : s.core.ptrs 55 < 0) (hR : s.core.ptrs 14 ≤ 0),
      ∃ (t : ℕ) (s' : State), Fr Q s s' t (fun z => z = s.core.ptrs 55) ∧ t ≤ 28 * m + 80 ∧ s'.core.pc = off + 283 ∧ s'.halted = false ∧ Env s' pts r c Z0 ∧ s'.core.ptrs 13 = s.core.ptrs 13 - 7 ∧ s'.core.ptrs 14 = s.core.ptrs 14 - 4 * m ∧ s'.core.ptrs 42 = s.core.ptrs 13 - 7 ∧ s'.core.ptrs 48 = s.core.ptrs 48 ∧ s'.core.ptrs 53 = k + 1 ∧ s'.core.ptrs 54 = s.core.ptrs 14 - 4 * m ∧ s'.core.ptrs 55 = s.core.ptrs 13 - 2 ∧ s'.integerMemory (s.core.ptrs 13 - 4) = 1 ∧ s'.integerMemory (s.core.ptrs 13 - 3) = s.core.ptrs 54 ∧ s'.integerMemory (s.core.ptrs 55) = s.core.ptrs 13 - 4 ∧ s'.integerMemory (s.core.ptrs 13 - 7) = s.core.ptrs 14 - 2 * m ∧ s'.integerMemory (s.core.ptrs 13 - 6) = s.core.ptrs 13 - 1 ∧ s'.integerMemory (s.core.ptrs 13 - 5) = s.core.ptrs 42 ∧ BoxAt s' (s.core.ptrs 14 - 2 * m) (setCoord lo k (thi ⟨k, hk⟩)) hi ∧ BoxAt s' (s.core.ptrs 14 - 4 * m) lo (setCoord hi k (thi ⟨k, hk⟩))) := by sorry

end DetANN.HPIM.BD
