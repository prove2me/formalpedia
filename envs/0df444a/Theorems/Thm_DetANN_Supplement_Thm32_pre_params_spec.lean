-- Prove2me | Theorems.Thm_DetANN_Supplement_Thm32_pre_params_spec
-- name    : DetANN.Supplement.Thm32.pre_params_spec
-- status  : Proved
-- author  : @milia
-- created : 2026-11-21T03:40:28.071662+00:00
-- url     : https://prove2.me/theorems/9274e192-527e-46c6-82d2-808b60a01942
-- title:
--   Parameters, factorials and initial signs of the construction program
-- statement:
--   Let $Q$ contain $\mathrm{pre}(q,o)$ at offset $o$. Let $s$ be a running state at $o+115$ with pointer 28 $=N$, pointer 3 $=d$, pointer 23 $=t_0\ge0$, real 5 $=\tau>0$, real 7 $=1$ and real 8 $=-1$. Write $p_0=\mathrm{momentOrder}\,N\,d$.
--
--   Then there are $T$ and $m$ such that the run is at $o+188$ after $T$ steps, has not halted, and:
--   - $q\,p_0\le2^m\tau^2$, and $2^{m'}\tau^2<q\,p_0$ for all $m'<m$;
--   - $T\le48+4N+40Nd+6m+40p_0+4\cdot2^m+5\cdot2^md$;
--   - pointer 14 holds $L=2^m$; pointer 34 holds $p_0$; pointers 36–39 hold $2p_0,2p_0+1,4p_0,4p_0+1$;
--   - pointers 40–46 hold the array bases $t_0,\ t_0+K_1,\ t_0+2K_1,\ t_0+3K_1,\ t_0+3K_1+P_1,\ t_0+3K_1+2P_1,\ t_0+3K_1+3P_1$, and pointer 23 holds $t_0+3K_1+4P_1$, where $K_1=4p_0+1$ and $P_1=2p_0+1$;
--   - pointer 15 holds $-d-1$, pointer 47 holds $Ld$; the other pointers in $[0,33)\cup(48,\infty)$ except 10, 11, 14, 15, 23 are unchanged;
--   - reals 9, 10, 11 hold $q$, $q\,p_0$, $\tau^2$; the reals other than 0–2 and 9–11 are unchanged;
--   - $\mathrm{mem}(t_0+i)=i!$ for $i\le4p_0$, and $\mathrm{mem}(-d-1-k)=-1$ for $k<Ld$;
--   - every other real cell is unchanged, the integer memory is unchanged, and the work grows by exactly $T$.
-- source:
--   Original, written for the mission 'Deterministic Approximate Nearest Neighbors in High Dimensions' as part of a proof of DetANN.Supplement.theorem_3_2 (Feng, Indyk, STOC 2027 submission, Theorem 3.2, p.7; the construction of §6.1, p.14, and Lemma 6.2). The machine is PNormReg (definition PNormReg_Machine) with the conventions of DetANN_DataStructure.

import Mathlib
import Definitions.Def_PNormReg_Machine
import Definitions.Def_DetANN_DataStructure
import Definitions.Def_PNormRegLib_Reloc
import Definitions.Def_DetANN_Sylvester
import Definitions.Def_DetANN_SignedBlocks
import Definitions.Def_DetANN_Supplement_EvProg
import Definitions.Def_DetANN_Supplement_PreProg
import Definitions.Def_DetANN_Supplement_PreDedup

namespace DetANN.Supplement.Thm32

open PNormReg PNormRegLib DetANN

/-- **Parameters and tables of `pre`.** From `off + 115` with `N` in pointer `28`, `d` in pointer `3`,
`top ≥ 0` in pointer `23`, `τ > 0` in real `5` and the constants `1`, `-1` in reals `7`, `8`, the program
`pre q` reaches `off + 188` with `p₀ = momentOrder N d` in pointer `34`, the repetition count
`L = 2^m` in pointer `14` (the least power of two with `q·p₀ ≤ L·τ²`), the arrays allocated from `top`,
the factorials `i!` (`i ≤ 4p₀`) at `top + i`, and the initial signs `-1` at the real cells
`-d-1-k` (`k < L·d`). -/
theorem pre_params_spec :
    ∀ (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (N d : ℕ)
    (top : ℤ) (τ : ℝ) (htop : 0 ≤ top) (hτ : 0 < τ) (s : State) (hpc : s.core.pc = off + 115)
    (hh : s.halted = false) (h28 : s.core.ptrs 28 = N) (h3 : s.core.ptrs 3 = d)
    (h23 : s.core.ptrs 23 = top) (h5 : s.core.regs 5 = τ) (h7 : s.core.regs 7 = 1)
    (h8 : s.core.regs 8 = -1),
    ∃ t m, (run Q s detTape t).core.pc = off + 188 ∧ (run Q s detTape t).halted = false ∧
      ((q : ℚ) : ℝ) * (momentOrder N d : ℝ) ≤ 2 ^ m * (τ * τ) ∧
      (∀ m' : ℕ, m' < m → 2 ^ m' * (τ * τ) < ((q : ℚ) : ℝ) * (momentOrder N d : ℝ)) ∧
      t ≤ 48 + 4 * N + 40 * (N * d) + 6 * m + 40 * momentOrder N d + 4 * 2 ^ m + 5 * (2 ^ m * d) ∧
      (run Q s detTape t).core.ptrs 14 = ((2 ^ m : ℕ) : ℤ) ∧
      (run Q s detTape t).core.ptrs 34 = momentOrder N d ∧
      (run Q s detTape t).core.ptrs 36 = 2 * (momentOrder N d : ℤ) ∧
      (run Q s detTape t).core.ptrs 37 = 2 * (momentOrder N d : ℤ) + 1 ∧
      (run Q s detTape t).core.ptrs 38 = 4 * (momentOrder N d : ℤ) ∧
      (run Q s detTape t).core.ptrs 39 = 4 * (momentOrder N d : ℤ) + 1 ∧
      (run Q s detTape t).core.ptrs 40 = top ∧
      (run Q s detTape t).core.ptrs 41 = top + (4 * (momentOrder N d : ℤ) + 1) ∧
      (run Q s detTape t).core.ptrs 42 = top + 2 * (4 * (momentOrder N d : ℤ) + 1) ∧
      (run Q s detTape t).core.ptrs 43 = top + 3 * (4 * (momentOrder N d : ℤ) + 1) ∧
      (run Q s detTape t).core.ptrs 44 =
        top + 3 * (4 * (momentOrder N d : ℤ) + 1) + (2 * (momentOrder N d : ℤ) + 1) ∧
      (run Q s detTape t).core.ptrs 45 =
        top + 3 * (4 * (momentOrder N d : ℤ) + 1) + 2 * (2 * (momentOrder N d : ℤ) + 1) ∧
      (run Q s detTape t).core.ptrs 46 =
        top + 3 * (4 * (momentOrder N d : ℤ) + 1) + 3 * (2 * (momentOrder N d : ℤ) + 1) ∧
      (run Q s detTape t).core.ptrs 23 =
        top + 3 * (4 * (momentOrder N d : ℤ) + 1) + 4 * (2 * (momentOrder N d : ℤ) + 1) ∧
      (run Q s detTape t).core.ptrs 15 = -(d : ℤ) - 1 ∧
      (run Q s detTape t).core.ptrs 47 = ((2 ^ m * d : ℕ) : ℤ) ∧
      (∀ y, y ≠ 10 → y ≠ 11 → y ≠ 14 → y ≠ 15 → y ≠ 23 → y < 33 ∨ 48 < y →
        (run Q s detTape t).core.ptrs y = s.core.ptrs y) ∧
      (run Q s detTape t).core.regs 9 = ((q : ℚ) : ℝ) ∧
      (run Q s detTape t).core.regs 10 = ((q : ℚ) : ℝ) * (momentOrder N d : ℝ) ∧
      (run Q s detTape t).core.regs 11 = τ * τ ∧
      (∀ y, y ≠ 0 → y ≠ 1 → y ≠ 2 → y ≠ 9 → y ≠ 10 → y ≠ 11 →
        (run Q s detTape t).core.regs y = s.core.regs y) ∧
      (∀ i : ℕ, i < 4 * momentOrder N d + 1 →
        (run Q s detTape t).core.mem (top + i) = (i.factorial : ℝ)) ∧
      (∀ k : ℕ, k < 2 ^ m * d → (run Q s detTape t).core.mem (-(d : ℤ) - 1 - k) = -1) ∧
      (∀ z, (z < top ∨ top + (4 * momentOrder N d + 1 : ℕ) ≤ z) →
        (-(d : ℤ) - 1 < z ∨ z ≤ -(d : ℤ) - 1 - ((2 ^ m * d : ℕ) : ℤ)) →
        (run Q s detTape t).core.mem z = s.core.mem z) ∧
      (run Q s detTape t).integerMemory = s.integerMemory ∧
      (run Q s detTape t).work = s.work + t := by sorry

end DetANN.Supplement.Thm32
