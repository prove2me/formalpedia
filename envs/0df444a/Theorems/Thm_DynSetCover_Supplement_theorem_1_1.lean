-- Prove2me | Theorems.Thm_DynSetCover_Supplement_theorem_1_1
-- name    : DynSetCover.Supplement.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T10:56:51.36947+00:00
-- url     : https://prove2.me/theorems/8f5db4ac-ace9-4351-891d-ab7e6601d15f
-- title:
--   Theorem 1.1 — constant worst-case recourse in polynomial time: $O(\log(n_t+1))$-approximation, $O(1)$ worst-case recourse, polynomial worst-case update time
-- statement:
--   There is a deterministic algorithm for fully dynamic weighted set cover that maintains an $O(\log(n_t+1))$-approximate cover with $O(1)$ worst-case recourse and polynomial worst-case update time, where $n_t=|A_t|$ is the number of active elements after update $t$; its approximation and recourse bounds are independent of the cost aspect ratio $C$.
--
--   Precisely: there are one program $P$ of the online word-RAM of §7 and one constant $c$ such that for every instance with positive rational costs, every valid update sequence, and every word size $W\ge c(\log_2(K+2)+1)$, where $K$ is the length of the instance encoding: every read of the input is reached; preprocessing takes at most $c(K+2)^c$ steps; and for every update $t$:
--   1. the update takes at most $c(K+2)^c$ steps;
--   2. its report consists of at most $c$ well-formed cover changes;
--   3. the maintained cover $C_t$ covers $A_t$;
--   4. the cost of $C_t$ satisfies
--   $$\sum_{S\in C_t}c_0(S)\le c\,\log_2(n_t+1)\,\mathrm{OPT}_0(A_t).$$
--
--   This answers the question of Gupta, Krishnaswamy, Kumar and Panigrahi whether constant worst-case recourse is achievable in polynomial time with logarithmic approximation. At $n_t=0$ the bound forces the maintained cover to be empty.
--
--   **Formalization Note** The input is the instance encoding followed by one word per update; time, report and maintained cover are measured between consecutive reads. The program receives neither the number of updates nor any bound on the active-set size.
--
--   Differences from the source:
--   - generalization: a fixed family $\mathcal F$ of subsets of $U$ whose union is $U$ → an indexed family $(S_s)_{s<m}$ of subsets of $U$ with union $U$, in which two indices may carry the same subset; reason: the paper's family is an injectively indexed one; no step of the argument uses that the sets are distinct
--   - reading: a deterministic algorithm, with no machine model named in the statement → one program of the online word-RAM of §7 (p.56): $W$-bit words, constant-time arithmetic, integer division, comparisons, bit operations and indirect table access, one step per instruction, for every word size $W\ge c(\log_2(K+2)+1)$; reason: the paper's only machine model is the word-RAM of §7 (p.56), which also carries the polynomial implementation of §3.3; a RAM program is deterministic
--   - encoding: the algorithm receives the set system and then the updates, and after each update returns its cover; update time; recourse (sets added to or removed from the cover per update) → the input is the word list: instance encoding of $K$ words, then one word per update ($2e$ insert, $2e+1$ delete); an update's time is the number of steps from its read to the next read; its report is the list of words written in between ($2s$ adds set $s$, $2s+1$ removes it), and its length is the recourse; $C_t$ is the effect of all words written before the next read; every read is reached; reason: the online protocol of the published base definitions; the report length is at least the number of sets added or removed
--   - reading: arbitrary positive costs $c_0(S)$ → the costs reach the program as positive rationals $c_0(S_s)=\mathrm{num}(s)/\mathrm{den}(s)$, numerator and denominator in binary; reason: a word-RAM receives encoded numbers; §7 speaks of 'the original cost encodings' (p.65)
--   - reading: polynomial worst-case update time → every update takes at most $c\,(K+2)^c$ steps, $K$ the length of the instance encoding, uniformly in $t$ and in the length of the update sequence; reason: polynomial in the input size; §3.3 (p.24) bounds each update's work by polynomially many searches over the $|\mathcal F|n_t$ set–level records and $O(n_t)$ copies, and $|\mathcal F|, n_t\le K$
--   - encoding: $O(\log(n_t+1))$-approximate, $O(1)$ recourse; approximation and recourse bounds independent of $C$ → one constant $c$, chosen before the instance, the update sequence and the word size: recourse $\le c$ and $\sum_{S\in C_t}c_0(S)\le c\log_2(n_t+1)\,\mathrm{OPT}_0(A_t)$; reason: standard; choosing $c$ first makes the bounds independent of the instance, in particular of the cost aspect ratio
--   - reading: the maintained cover $C_t$ → $C_t$ covers $A_t$ is stated as a clause, and its reports are well formed (every word names a set); reason: in fully dynamic set cover the maintained subfamily covers all active elements (p.1); the cost bound alone does not say so
--   - generalization: no preprocessing bound is stated in Theorem 1.1 → the steps before the first update is read are at most $c\,(K+2)^c$; reason: an added conclusion (the polynomial preprocessing of Theorems 7.5 and 7.6); it specializes to the source by dropping it
-- source:
--   Paul, Solomon, Weighted Set Cover with Constant Worst-Case Recourse: From Exponential to Best-Known Update Time (STOC 2027 submission, preprint, sha256 a671756b983353737f48798343a4d176654843ba40cd482f54283402087c5cb0), Theorem 1.1, p.2 (PDF 4); polynomial implementation §3.3, pp.23–24 (PDF 25–26); machine model §7, p.56 (PDF 58)

import Mathlib
import Definitions.Def_DynSetCover_Protocol

namespace DynSetCover.Supplement

/-- **Theorem 1.1 (Constant worst-case recourse in polynomial time)** (Paul, Solomon, *Weighted
Set Cover with Constant Worst-Case Recourse: From Exponential to Best-Known Update Time*, STOC
2027 submission, sha256 a671756b…, p.2 (PDF 4)). There is a deterministic algorithm for fully
dynamic weighted set cover that maintains an `O(log(n_t + 1))`-approximate cover with `O(1)`
worst-case recourse and polynomial worst-case update time. Its approximation and recourse bounds
are independent of the cost aspect ratio `C`.

There are one program `P` of the online word-RAM and one constant `c`, fixed before everything
else, such that for every instance with rational costs, every valid update sequence, and every
word size `W ≥ c(log₂(K + 2) + 1)` (`K` the length of the instance encoding): every read of the
input is reached; preprocessing takes at most `c(K + 2)^c` steps; and every update `t` takes at
most `c(K + 2)^c` steps, reports at most `c` well-formed cover changes, and leaves a maintained
cover `C_t` that covers `A_t` and costs at most `c·log₂(n_t + 1)·OPT0(A_t)`, `n_t = |A_t|`.

**Formalization Note.** The machine is the online word-RAM `DRAM` of §7 (p.56) with one step per
instruction; a RAM program is deterministic. The input is `input inst num den σ`: the instance
encoding (`K` words: sizes, elements, and the bits of each cost's numerator and denominator),
then one word per update, so update `t` is read by read number `K + t`. Its time is the number
of steps from that read to the next read, its report (recourse) is the list of words written in
between, and `C_t` is the effect of all words written before the next read. "Polynomial update
time" is read as polynomial in the input encoding length `K`, uniformly in `t` and in the length
of the update sequence. The program is not given the number of updates or the active sets. The
costs reach the program as positive rationals, numerator and denominator in binary
(`RatCosts`). The preprocessing clause is an added polynomial bound on the steps before the
first update is read. -/
theorem theorem_1_1 :
    ∃ (P : Program) (c : ℕ), ∀ (inst : Instance) (num den : Fin inst.m → ℕ), RatCosts inst num den →
      ∀ σ : List (Upd inst.u), Valid σ →
      ∀ W : ℕ, c * (Nat.log 2 ((enc inst num den).length + 2) + 1) ≤ W →
      let K := (enc inst num den).length
      let inp := input inst num den σ
      ∃ τ : ℕ → ℕ,
        (∀ k, 1 ≤ k → k ≤ K + σ.length + 1 → ReadsAt W P inp k (τ k)) ∧
        τ (K + 1) ≤ c * (K + 2) ^ c ∧
        ∀ t, 1 ≤ t → t ≤ σ.length →
          τ (K + t + 1) - τ (K + t) ≤ c * (K + 2) ^ c ∧
          (report W P inp τ (K + t)).length ≤ c ∧
          WellFormed inst.m (report W P inp τ (K + t)) ∧
          inst.Covers (coverAfter inst.m W P inp τ (K + t)) (active σ t) ∧
          inst.cost0 (coverAfter inst.m W P inp τ (K + t)) ≤
            (c : ℝ) * Real.logb 2 ((active σ t).card + 1 : ℝ) * inst.OPT0 (active σ t) := by sorry

end DynSetCover.Supplement
