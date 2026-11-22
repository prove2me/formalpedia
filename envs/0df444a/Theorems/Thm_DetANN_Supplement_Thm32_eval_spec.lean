-- Prove2me | Theorems.Thm_DetANN_Supplement_Thm32_eval_spec
-- name    : DetANN.Supplement.Thm32.eval_spec
-- status  : Proved
-- author  : @milia
-- created : 2026-11-21T07:12:31.786505+00:00
-- url     : https://prove2.me/theorems/e40d38a4-2e6a-4131-af1e-7e7be06f0c04
-- title:
--   The subroutine EVAL of the construction program computes the conditional expectation of Lemma 6.2
-- statement:
--   Let $Q$ contain $\mathrm{pre}(q,o)$ (definition `DetANN_Supplement_PreProg`) at offset $o$. Let $k,L,p_0$ with $L\ge1$, a sign index $kk<L\cdot2^k$, $\tau>0$, a duplicate-free list $l$ of nonzero vectors of $\mathbb R^{2^k}$, signs $\xi$, and integers $H_b\ge0$, $D_b$, $t_0$ with $H_b+4^k\le D_b$ and $D_b+|l|\,2^k\le t_0$. Write $K_1=4p_0+1$ and $P_1=2p_0+1$.
--
--   Let $s$ be a running state at $o+206$ (the entry of `EVAL`) with:
--   - pointer 50 equal to the return flag $\mathrm{ret}\in\{0,1\}$ and pointer 48 equal to $kk$;
--   - pointers $0,1,3,14,15,24,26,27$ equal to $0,1,2^k,L,-2^k-1,H_b,D_b,D_b+|l|2^k$;
--   - pointers $36,37,39$ equal to $2p_0,2p_0+1,4p_0+1$;
--   - pointers $40$–$46$ equal to the array bases $t_0,\ t_0+K_1,\ t_0+2K_1,\ t_0+3K_1,\ t_0+3K_1+P_1,\ t_0+3K_1+2P_1,\ t_0+3K_1+3P_1$;
--   - reals $5,6,7$ equal to $\tau,0,1$;
--   - in memory: the Sylvester columns $\mathrm{mem}(H_b+r2^k+j)=\mathrm{sylvester}\,k\,j\,r$, the table $\mathrm{TableAt}(\mathrm{mem},D_b,l)$ (definition `DetANN_Supplement_PreDedup`), the factorials $\mathrm{mem}(t_0+i)=i!$ for $i\le4p_0$, and $\mathrm{SignsAt}(\mathrm{mem},L,k,\xi)$ (definition `DetANN_Supplement_Greedy`).
--
--   Then for some $T\le\mathrm{evalB}(|l|,2^k,L,p_0)$ the run of $Q$ from $s$ is, after $T$ steps, at $o+194$ if $\mathrm{ret}=0$ and at $o+198$ if $\mathrm{ret}=1$, has not halted, and
--   $$\text{real }13=\mathrm{lemma62Expr}\big(\mathrm{sylvester}\,k,\ L,\ \tau,\ p_0,\ \mathrm{toFinset}(l),\ \mathrm{prefixMask}(L,2^k,kk+1),\ \xi\big).$$
--   Moreover:
--   - only pointers $5,10,11,12,16$–$20,31,51$–$58$ and reals $0,1,13$–$24$ change;
--   - only the real cells in $[t_0+K_1,\ t_0+3K_1+4P_1)$ change;
--   - the integer memory is unchanged, and the work grows by exactly $T$.
-- source:
--   Original, written for the mission 'Deterministic Approximate Nearest Neighbors in High Dimensions' as part of a proof of DetANN.Supplement.theorem_3_2 (Feng, Indyk, STOC 2027 submission, Theorem 3.2, p.7; the construction of §6.1, p.14, and the conditional expectation of Lemma 6.2). The machine is PNormReg (definition PNormReg_Machine) with the conventions of DetANN_DataStructure.

import Mathlib
import Definitions.Def_PNormReg_Machine
import Definitions.Def_DetANN_DataStructure
import Definitions.Def_PNormRegLib_Reloc
import Definitions.Def_DetANN_Sylvester
import Definitions.Def_DetANN_SignedBlocks
import Definitions.Def_DetANN_SignChoice
import Definitions.Def_DetANN_Supplement_PreProg
import Definitions.Def_DetANN_Supplement_PreDedup
import Definitions.Def_DetANN_Supplement_Greedy

namespace DetANN.Supplement.Thm32

open PNormReg PNormRegLib DetANN

/-- **The subroutine `EVAL` of `pre` computes the conditional expectation of Lemma 6.2.** Called at
`off + 206` with return flag `ret ∈ {0, 1}` in pointer `50` and the sign index `kk` in pointer `48`, with
the Sylvester columns at `Hb`, the duplicate-free table `l` of nonzero vectors at `Db`, the factorials
`i!` (`i ≤ 4p₀`) at `t0` and the signs `ξ` in their cells, it returns to `off + 194` (`ret = 0`) or
`off + 198` (`ret = 1`) within `evalB |l| 2^k L p₀` steps with
`lemma62Expr (sylvester k) L τ p₀ l.toFinset (prefixMask L 2^k (kk+1)) ξ` in real `13`. It changes only
scratch registers and the scratch arrays `[t0 + 4p₀ + 1, t0 + 3(4p₀+1) + 4(2p₀+1))`. -/
theorem eval_spec :
    ∀ (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (k L p₀ kk : ℕ) (hL : 1 ≤ L)
    (hkk : kk < L * 2 ^ k) (τ : ℝ) (hτ : 0 < τ) (l : List (EuclideanSpace ℝ (Fin (2 ^ k))))
    (hl : l.Nodup) (hl0 : ∀ v ∈ l, v ≠ 0) (ξ : Fin L → Fin (2 ^ k) → Bool) (Hb Db t0 ret : ℤ)
    (hHD : Hb + ((2 ^ k * 2 ^ k : ℕ) : ℤ) ≤ Db) (hDt : Db + ((l.length * 2 ^ k : ℕ) : ℤ) ≤ t0)
    (hH0 : 0 ≤ Hb) (hret : ret = 0 ∨ ret = 1) (s : State)
    (hpc : s.core.pc = off + 206) (hh : s.halted = false)
    (h0 : s.core.ptrs 0 = 0) (h1 : s.core.ptrs 1 = 1) (h3 : s.core.ptrs 3 = ((2 ^ k : ℕ) : ℤ))
    (h14 : s.core.ptrs 14 = L) (h15 : s.core.ptrs 15 = -((2 ^ k : ℕ) : ℤ) - 1)
    (h24 : s.core.ptrs 24 = Hb) (h26 : s.core.ptrs 26 = Db)
    (h27 : s.core.ptrs 27 = Db + ((l.length * 2 ^ k : ℕ) : ℤ))
    (h36 : s.core.ptrs 36 = 2 * (p₀ : ℤ)) (h37 : s.core.ptrs 37 = 2 * (p₀ : ℤ) + 1)
    (h39 : s.core.ptrs 39 = 4 * (p₀ : ℤ) + 1) (h40 : s.core.ptrs 40 = t0)
    (h41 : s.core.ptrs 41 = t0 + (4 * (p₀ : ℤ) + 1))
    (h42 : s.core.ptrs 42 = t0 + 2 * (4 * (p₀ : ℤ) + 1))
    (h43 : s.core.ptrs 43 = t0 + 3 * (4 * (p₀ : ℤ) + 1))
    (h44 : s.core.ptrs 44 = t0 + 3 * (4 * (p₀ : ℤ) + 1) + (2 * (p₀ : ℤ) + 1))
    (h45 : s.core.ptrs 45 = t0 + 3 * (4 * (p₀ : ℤ) + 1) + 2 * (2 * (p₀ : ℤ) + 1))
    (h46 : s.core.ptrs 46 = t0 + 3 * (4 * (p₀ : ℤ) + 1) + 3 * (2 * (p₀ : ℤ) + 1))
    (h48 : s.core.ptrs 48 = kk) (h50 : s.core.ptrs 50 = ret)
    (h5 : s.core.regs 5 = τ) (h6 : s.core.regs 6 = 0) (h7 : s.core.regs 7 = 1)
    (hcol : ∀ r j : Fin (2 ^ k), s.core.mem (Hb + (((r : ℕ) * 2 ^ k + j : ℕ) : ℤ)) = sylvester k j r)
    (hT : TableAt s.core.mem Db l)
    (hF : ∀ i : ℕ, i < 4 * p₀ + 1 → s.core.mem (t0 + i) = (i.factorial : ℝ))
    (hS : SignsAt s.core.mem L k ξ),
    ∃ t, t ≤ evalB l.length (2 ^ k) L p₀ ∧
      (ret = 0 → (run Q s detTape t).core.pc = off + 194) ∧
      (ret = 1 → (run Q s detTape t).core.pc = off + 198) ∧
      (run Q s detTape t).halted = false ∧
      (run Q s detTape t).core.regs 13 =
        lemma62Expr (sylvester k) L τ p₀ l.toFinset (prefixMask L (2 ^ k) (kk + 1)) ξ ∧
      (∀ y, y ≠ 5 → y ≠ 10 → y ≠ 11 → y ≠ 12 → y ≠ 16 → y ≠ 17 → y ≠ 18 → y ≠ 19 → y ≠ 20 →
        y ≠ 31 → (y < 51 ∨ 58 < y) → (run Q s detTape t).core.ptrs y = s.core.ptrs y) ∧
      (∀ y, y ≠ 0 → y ≠ 1 → (y < 13 ∨ 24 < y) → (run Q s detTape t).core.regs y = s.core.regs y) ∧
      (∀ z, (z < t0 + (4 * (p₀ : ℤ) + 1) ∨
          t0 + 3 * (4 * (p₀ : ℤ) + 1) + 4 * (2 * (p₀ : ℤ) + 1) ≤ z) →
        (run Q s detTape t).core.mem z = s.core.mem z) ∧
      (run Q s detTape t).integerMemory = s.integerMemory ∧
      (run Q s detTape t).work = s.work + t := by sorry

end DetANN.Supplement.Thm32
