-- Prove2me | Theorems.Thm_DynSetCover_theorem_1_2
-- name    : DynSetCover.theorem_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:45:08.944203+00:00
-- url     : https://prove2.me/theorems/d73bf7fd-f9c7-45ff-b34d-8a654c4253ce
-- title:
--   Theorem 1.2 — fast update time and constant recourse, both worst-case
-- statement:
--   There is a deterministic algorithm for fully dynamic weighted set cover that simultaneously maintains an $O(\log n)$-approximate cover with $O(1)$ worst-case recourse and $O(f\log n)$ worst-case update time, with bounds independent of the cost aspect ratio.
--
--   Precisely: there are one program $P$ of the online word-RAM of §7 and one constant $c$, fixed before everything else, such that for every instance with rational costs, every valid update sequence, every word size $W\ge c(\log_2(K+2)+1)$ ($K$ the length of the instance encoding) and every $n\ge2$ with $|A_t|\le n$ for all $t$:
--   1. every read of the input is reached, and preprocessing takes at most $c(K+2)^c$ steps;
--   2. every update $t$ takes at most $c\,f\log_2 n$ steps;
--   3. its report consists of at most $c$ well-formed cover changes;
--   4. the maintained cover $C_t$ covers $A_t$ and
--   $$\sum_{S\in C_t}c_0(S)\le c\,\log_2 n\cdot\mathrm{OPT}_0(A_t).$$
--
--   Here $f$ is the frequency. Since $c$ is chosen before the instance, the bounds do not depend on the cost aspect ratio $\max c_0/\min c_0$. This answers the question of Gupta, Krishnaswamy, Kumar and Panigrahi (STOC 2017) on constant worst-case recourse in polynomial time, with the best known update time.
--
--   **Formalization Note** The program is not given $n$, the number of updates or the active sets; time, report and cover are measured between consecutive reads of the input.
--
--   Differences from the source:
--   - generalization: a fixed family $\mathcal F$ of subsets of $U$ whose union is $U$ → an indexed family $(S_s)_{s<m}$ of subsets of $U$ with union $U$, in which two indices may carry the same subset; reason: the paper's family is an injectively indexed one; no step of the argument uses that the sets are distinct
--   - reading: a deterministic algorithm, with no machine model named in the statement → one program of the online word-RAM of §7 (p.56): $W$-bit words, constant-time arithmetic, integer division, comparisons, bit operations and indirect table access, one step per instruction, for every word size $W\ge c(\log_2(K+2)+1)$; reason: the proof is Theorem 7.5, stated 'in the stated word-RAM model' of p.56, whose words hold addresses, cost exponents and $O(\log N)$-bit integers; a RAM program is deterministic
--   - encoding: the algorithm receives the set system and then the updates, and after each update returns its cover; update time; recourse (sets added to or removed from the cover per update) → the input is the word list: instance encoding of $K$ words, then one word per update ($2e$ insert, $2e+1$ delete); an update's time is the number of steps from its read to the next read; its report is the list of words written in between ($2s$ adds set $s$, $2s+1$ removes it), and its length is the recourse; $C_t$ is the effect of all words written before the next read; reason: reading one element in one word is the §7 model (a bit-by-bit input would cost $\Theta(\log|U|)$ steps per update); the report length is at least the number of sets added or removed
--   - reading: a fixed positive cost $c_0(S)$ → the costs reach the program as positive rationals $c_0(S_s)=\mathrm{num}(s)/\mathrm{den}(s)$, numerator and denominator in binary; reason: a word-RAM receives encoded numbers; §7 speaks of 'the original cost encodings' and 'the encoded size of the fixed set system' (p.65)
--   - reading: 'Let $n\ge2$ bound the number of active elements' → $n\ge2$ is quantified after the program is fixed, with $|A_t|\le n$ for every $t$; the program does not receive $n$; reason: the stronger of the two readings; §7.5 (Theorem 7.6) proves it without an advance bound on the active-set size
--   - encoding: $O(1)$ worst-case recourse → each update's report has at most $c$ words; reason: the report lists the cover changes; its length bounds the number of sets added to or removed from the cover
--   - encoding: $O(\cdot)$ bounds and 'polynomial time' → one constant $c$, chosen before the instance, the update sequence and the word size, with explicit bounds $c\cdot(\dots)$ and $c(\cdot)^c$; reason: standard; choosing $c$ first makes the bounds independent of the instance, in particular of the cost aspect ratio
--   - generalization: (no preprocessing clause in the statement) → preprocessing takes at most $c(K+2)^c$ steps; reason: an added conclusion proved in the paper ('after polynomial preprocessing', Theorems 7.5 and 7.6); it rules out unbounded table precomputation
-- source:
--   Paul, Solomon, Weighted Set Cover with Constant Worst-Case Recourse: From Exponential to Best-Known Update Time (STOC 2027 submission, preprint, sha256 a671756b983353737f48798343a4d176654843ba40cd482f54283402087c5cb0), Theorem 1.2, p.3 (PDF 5)

import Mathlib
import Definitions.Def_DynSetCover_Protocol

namespace DynSetCover

/-- **Theorem 1.2 (Fast update time and constant recourse, both worst-case)** (Paul, Solomon,
*Weighted Set Cover with Constant Worst-Case Recourse: From Exponential to Best-Known Update
Time*, STOC 2027 submission, sha256 a671756b…, p.3 (PDF 5)). There is a deterministic algorithm
for fully dynamic weighted set cover that simultaneously maintains an `O(log n)`-approximate
cover with `O(1)` worst-case recourse and `O(f log n)` worst-case update time. The bounds are
independent of the cost aspect ratio `C`.

There are one program `P` of the online word-RAM and one constant `c`, fixed before everything
else, such that for every instance, every valid update sequence, every word size
`W ≥ c(log₂(K + 2) + 1)` (`K` the length of the instance encoding), and every `n ≥ 2` bounding
`|A_t|` for all `t`: every read of the input is reached; preprocessing takes at most `c(K + 2)^c`
steps; and every update `t` takes at most `c·f·log₂ n` steps, reports at most `c` well-formed
cover changes, and leaves a maintained cover `C_t` that covers `A_t` and costs at most
`c·log₂ n·OPT0(A_t)`.

**Formalization Note.** The machine is the online word-RAM `DRAM` of §7 (p.56) with one step per
instruction; a RAM program is deterministic. The input is `input inst num den σ`: the instance encoding
(`K` words: sizes, elements, and the bits of each cost's numerator and denominator), then one
word per update, so update `t` is read by read number `K + t`. Its time is the number of steps
from that read to the next read, its report (recourse) is the list of words written in between,
and `C_t` is the effect of all words written before the next read. The program is not given `n`,
the number of updates, or the active sets. The costs reach the program as positive rationals,
numerator and denominator in binary (`RatCosts`). The preprocessing
clause is the polynomial preprocessing of Theorems 7.5 and 7.6. -/
theorem theorem_1_2 :
    ∃ (P : Program) (c : ℕ), ∀ (inst : Instance) (num den : Fin inst.m → ℕ), RatCosts inst num den →
      ∀ σ : List (Upd inst.u), Valid σ →
      ∀ W : ℕ, c * (Nat.log 2 ((enc inst num den).length + 2) + 1) ≤ W →
      ∀ n : ℕ, 2 ≤ n → (∀ t ≤ σ.length, (active σ t).card ≤ n) →
      let K := (enc inst num den).length
      let inp := input inst num den σ
      ∃ τ : ℕ → ℕ,
        (∀ k, 1 ≤ k → k ≤ K + σ.length + 1 → ReadsAt W P inp k (τ k)) ∧
        τ (K + 1) ≤ c * (K + 2) ^ c ∧
        ∀ t, 1 ≤ t → t ≤ σ.length →
          τ (K + t + 1) - τ (K + t) ≤ c * inst.freq * Nat.log 2 n ∧
          (report W P inp τ (K + t)).length ≤ c ∧
          WellFormed inst.m (report W P inp τ (K + t)) ∧
          inst.Covers (coverAfter inst.m W P inp τ (K + t)) (active σ t) ∧
          inst.cost0 (coverAfter inst.m W P inp τ (K + t)) ≤
            (c : ℝ) * Real.logb 2 (n : ℝ) * inst.OPT0 (active σ t) := by sorry

end DynSetCover
