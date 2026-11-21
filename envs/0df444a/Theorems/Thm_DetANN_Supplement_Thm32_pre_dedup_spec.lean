-- Prove2me | Theorems.Thm_DetANN_Supplement_Thm32_pre_dedup_spec
-- name    : DetANN.Supplement.Thm32.pre_dedup_spec
-- status  : Proved
-- author  : @milia
-- created : 2026-11-21T03:40:20.77763+00:00
-- url     : https://prove2.me/theorems/f3bc94ec-9837-4e4c-b7ca-58c6428c048a
-- title:
--   The dedupe loop of the construction program
-- statement:
--   Let $Q$ contain $\mathrm{pre}(q,o)$ at offset $o$, let $d\ge1$, and let $x:\mathbb N\to\mathbb R^d$ with the points $x_i$ ($i<n$) in the real cells $1+id+c$. Let $s$ be a running state at $o+67$ with pointer 22 $=n$, pointer 3 $=d$ and pointer 23 $=D_b\ge1+nd$.
--
--   Then for some $T\le n\big(n\cdot\mathrm{pairB}(d,n^2)+8\big)+7$ the run is at $o+115$ after $T$ steps, has not halted, and:
--   - $\mathrm{TableAt}(\mathrm{mem},D_b,\mathrm{ddList}(x,n))$ (definition `DetANN_Supplement_PreDedup`);
--   - pointer 28 holds $|\mathrm{ddList}(x,n)|$, pointer 26 holds $D_b$, pointer 23 holds $D_b+|\mathrm{ddList}(x,n)|\cdot d$;
--   - the pointers other than 10, 11, 20, 23, 26–32 and the reals other than 0–2 are unchanged;
--   - the real cells below $D_b$ and the integer memory are unchanged, and the work grows by exactly $T$.
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

/-- **The dedupe loop of `pre`.** From `off + 67`, with the points `x i` at the real cells `1 + i·d`
and `top = Db ≥ 1 + n·d`, the program `pre q` reaches `off + 115` with the list `ddList x n`
(definition `DetANN_Supplement_PreDedup`) stored at `Db` (`TableAt`), its length in pointer `28` and
`top = Db + |ddList x n|·d`. Cells below `Db` are unchanged. -/
theorem pre_dedup_spec :
    ∀ {d : ℕ} (Q : Program) (off : ℕ) (q : ℚ) (hE : Embeds Q (pre q off) off) (hd1 : 1 ≤ d)
    (n : ℕ) (x : ℕ → EuclideanSpace ℝ (Fin d)) (Db : ℤ) (hDb : ((1 + n * d : ℕ) : ℤ) ≤ Db)
    (s : State) (hpc : s.core.pc = off + 67) (hh : s.halted = false)
    (h22 : s.core.ptrs 22 = n) (h3 : s.core.ptrs 3 = d) (h23 : s.core.ptrs 23 = Db)
    (hx : ∀ i' : ℕ, i' < n → ∀ c : Fin d, s.core.mem ((1 + i' * d + c : ℕ) : ℤ) = x i' c),
    ∃ t, t ≤ n * (n * pairB d (n * n) + 8) + 7 ∧ (run Q s detTape t).core.pc = off + 115 ∧
      (run Q s detTape t).halted = false ∧
      (run Q s detTape t).core.ptrs 23 = Db + (((ddList x n).length * d : ℕ) : ℤ) ∧
      (run Q s detTape t).core.ptrs 28 = (ddList x n).length ∧
      (run Q s detTape t).core.ptrs 26 = Db ∧
      (∀ y, y ≠ 10 → y ≠ 11 → y ≠ 20 → y ≠ 23 → y ≠ 26 → y ≠ 27 → y ≠ 28 → y ≠ 29 → y ≠ 30 →
        y ≠ 31 → y ≠ 32 → (run Q s detTape t).core.ptrs y = s.core.ptrs y) ∧
      (∀ y, y ≠ 0 → y ≠ 1 → y ≠ 2 → (run Q s detTape t).core.regs y = s.core.regs y) ∧
      TableAt (run Q s detTape t).core.mem Db (ddList x n) ∧
      (∀ z, z < Db → (run Q s detTape t).core.mem z = s.core.mem z) ∧
      (run Q s detTape t).integerMemory = s.integerMemory ∧
      (run Q s detTape t).work = s.work + t := by sorry

end DetANN.Supplement.Thm32
