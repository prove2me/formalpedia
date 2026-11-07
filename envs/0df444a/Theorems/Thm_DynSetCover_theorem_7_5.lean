-- Prove2me | Theorems.Thm_DynSetCover_theorem_7_5
-- name    : DynSetCover.theorem_7_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:46:07.035225+00:00
-- url     : https://prove2.me/theorems/26f5dbeb-e7c4-4540-8efa-2f2c63c39d88
-- title:
--   Theorem 7.5 — implementation bounds: $O(f\log N)$ time per update, $O(I+(|\mathcal F|+N)\log N)$ words, polynomial preprocessing
-- statement:
--   Consider the faster algorithm of §5 with a capacity bound $N\ge2$ supplied after the instance and replaced at initialization by $\max\{2,\min\{N,|U|\}\}$. There are a program $P$ of the online word-RAM of §7 and a constant $c$ such that for every instance with rational costs, every $N\ge2$, every valid update sequence with $|A_t|\le N$ throughout, and every word size $W\ge c(\log_2(K+N+2)+1)$, where $K$ is the length of the instance encoding:
--   1. every read of the input is reached, and preprocessing (the steps before the first update is read) takes at most $c(K+N+2)^c$ steps;
--   2. each update takes at most $c\,f\log_2N$ steps, and its report consists of at most $c$ well-formed cover changes;
--   3. over the whole run, at most $c\,(I+(|\mathcal F|+N)(\log_2N+1))$ memory cells are written, plus the number of cost-bit words of the input ("in addition to the original cost encodings");
--   4. the maintained covers are the physical covers at the update boundaries of an admissible run of the §5 algorithm with capacity $\max\{2,\min\{N,|U|\}\}$.
--
--   Here $f$ is the frequency and $I=\sum_{S\in\mathcal F}|S|$.
--
--   **Formalization Note** The input is the instance encoding, then $N$ in one word, then one word per update; the time of an update is the number of steps from its read to the next read, its report is what is written in between, and its maintained cover is the effect of everything written before the next read.
--
--   Differences from the source:
--   - generalization: a fixed family $\mathcal F$ of subsets of $U$ whose union is $U$ → an indexed family $(S_s)_{s<m}$ of subsets of $U$ with union $U$, in which two indices may carry the same subset; reason: the paper's family is an injectively indexed one; no step of the argument uses that the sets are distinct
--   - reading: 'in the stated word-RAM model' → one program of the online word-RAM of §7 for every word size $W\ge c(\log_2(K+N+2)+1)$; reason: the model of p.56: words hold input addresses, cost exponents and $O(\log N)$-bit integers
--   - encoding: the algorithm receives the set system and then the updates, and after each update returns its cover; update time; recourse (sets added to or removed from the cover per update) → the input is the word list: instance encoding of $K$ words, then one word per update ($2e$ insert, $2e+1$ delete); an update's time is the number of steps from its read to the next read; its report is the list of words written in between ($2s$ adds set $s$, $2s+1$ removes it), and its length is the recourse; $C_t$ is the effect of all words written before the next read; reason: reading one element in one word is the §7 model (a bit-by-bit input would cost $\Theta(\log|U|)$ steps per update); the report length is at least the number of sets added or removed
--   - reading: a fixed positive cost $c_0(S)$ → the costs reach the program as positive rationals $c_0(S_s)=\mathrm{num}(s)/\mathrm{den}(s)$, numerator and denominator in binary; reason: a word-RAM receives encoded numbers; §7 speaks of 'the original cost encodings' and 'the encoded size of the fixed set system' (p.65)
--   - encoding: the implementation uses $O(I+(|\mathcal F|+N)\log N)$ words, in addition to the original cost encodings → the number of distinct memory cells written during the whole run is at most $c(I+(|\mathcal F|+N)(\log_2N+1))$ plus the number of cost-bit words; reason: all allocation is from preallocated pools (p.56), so the space used is the set of cells ever written
--   - encoding: $O(\cdot)$ bounds and 'polynomial time' → one constant $c$, chosen before the instance, the update sequence and the word size, with explicit bounds $c\cdot(\dots)$ and $c(\cdot)^c$; reason: standard; choosing $c$ first makes the bounds independent of the instance, in particular of the cost aspect ratio
--   - reading: 'the implementation' of the faster algorithm → the maintained covers equal the physical covers at the boundaries of an admissible run with capacity $\max\{2,\min\{N,|U|\}\}$, for some choice of cheapest sets; reason: the mission formalizes the §5 algorithm as its admissible runs (the paper's FIFO run is one of them); the capacity replacement is stated on p.56
--   - generalization: (no recourse clause in the statement) → each report has at most $c$ words; reason: an added conclusion proved in the paper: 'the implementation also preserves constant worst-case recourse' (proof, p.65)
-- source:
--   Paul, Solomon, Weighted Set Cover with Constant Worst-Case Recourse: From Exponential to Best-Known Update Time (STOC 2027 submission, preprint, sha256 a671756b983353737f48798343a4d176654843ba40cd482f54283402087c5cb0), Theorem 7.5, p.65 (PDF 67); capacity replacement and machine model, p.56 (PDF 58)

import Mathlib
import Definitions.Def_DynSetCover_Protocol
import Definitions.Def_DynSetCover_Algorithm

namespace DynSetCover

/-- **Theorem 7.5 (Implementation bounds)** (Paul, Solomon, STOC 2027 submission, sha256
a671756b…, p.65 (PDF 67)). In the stated word-RAM model, each input update takes `O(f log N)`
worst-case time. Writing `I = Σ_{S∈F} |S|`, the implementation uses `O(I + (|F| + N) log N)`
words, in addition to the original cost encodings. Preprocessing takes polynomial time in `N`
and the encoded size of the fixed set system.

Here the implementation is of the §5 algorithm with the capacity bound `N` supplied after the
instance, replaced at initialization by `max{2, min{N, |U|}}` (p.56). There are one program `P`
and one constant `c` such that for every instance, every `N ≥ 2`, every valid update sequence
with `|A_t| ≤ N` throughout, and every word size `W ≥ c(log₂(K + N + 2) + 1)` (`K` the length of
the instance encoding): every read of the input is reached; preprocessing (the steps before the
first update is read) takes at most `c(K + N + 2)^c` steps; each update takes at most
`c·f·log₂ N` steps and reports at most `c` well-formed cover changes; over the whole run at most
`c(I + (|F| + N)(log₂ N + 1))` memory cells plus the number of cost-bit words of the input are
written; and the maintained covers are the physical covers at the update boundaries of an
admissible run of the §5 algorithm with capacity `max{2, min{N, |U|}}`.

**Formalization Note.** The machine is the online word-RAM `DRAM` (§7, p.56). The input is
`inputCap inst num den N σ`: the instance encoding (`K` words), `N` in one word, then one word per
update, so update `t` is read by read number `K + 1 + t`. The time of update `t` is the number
of steps from its read to the next read; its report is the words written in between; the
maintained cover is the effect of all words written before the next read. "Uses … words" is the
number of distinct memory cells written during the whole run. -/
theorem theorem_7_5 :
    ∃ (P : Program) (c : ℕ), ∀ (inst : Instance) (num den : Fin inst.m → ℕ), RatCosts inst num den → ∀ N : ℕ, 2 ≤ N →
      ∀ σ : List (Upd inst.u), Valid σ → (∀ t ≤ σ.length, (active σ t).card ≤ N) →
      ∀ W : ℕ, c * (Nat.log 2 ((enc inst num den).length + N + 2) + 1) ≤ W →
      let K := (enc inst num den).length + 1
      let inp := inputCap inst num den N σ
      ∃ τ : ℕ → ℕ,
        (∀ k, 1 ≤ k → k ≤ K + σ.length + 1 → ReadsAt W P inp k (τ k)) ∧
        τ (K + 1) ≤ c * ((enc inst num den).length + N + 2) ^ c ∧
        (∀ t, 1 ≤ t → t ≤ σ.length →
          τ (K + t + 1) - τ (K + t) ≤ c * inst.freq * Nat.log 2 N ∧
          (report W P inp τ (K + t)).length ≤ c ∧
          WellFormed inst.m (report W P inp τ (K + t))) ∧
        (conf W P inp (τ (K + σ.length + 1))).written.card ≤
          c * (inst.totalSize + (inst.m + N) * (Nat.log 2 N + 1)) + costBits inst num den ∧
        ∃ ce : Fin inst.u → Fin inst.m, inst.IsCheapest ce ∧
          ∃ bs : ℕ → State inst, IsRun inst (max 2 (min N inst.u)) ce σ bs ∧
            ∀ t, 1 ≤ t → t ≤ σ.length →
              coverAfter inst.m W P inp τ (K + t) = physCover inst (bs t) := by sorry

end DynSetCover
