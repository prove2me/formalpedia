-- Prove2me | Theorems.Thm_DynSetCover_theorem_7_6
-- name    : DynSetCover.theorem_7_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:44:55.83498+00:00
-- url     : https://prove2.me/theorems/26df52b7-3584-4e3b-a4cb-cdb94d246008
-- title:
--   Theorem 7.6 — $O(f\log(n_t+2))$ time, $O(1)$ recourse and $2048(1+\ln\Delta_t)$-approximation without an advance bound
-- statement:
--   There are a program $P$ of the online word-RAM of §7 and a constant $c$ such that for every instance with rational costs, every valid update sequence (the program receives no bound on the active-set size), and every word size $W\ge c(\log_2(K+2)+1)$, where $K$ is the length of the instance encoding: every read of the input is reached; preprocessing takes at most $c(K+2)^c$ steps; and for every update $t$, with $n_t=|A_t|$:
--   1. the update takes at most $c\,f\log_2(n_t+2)$ steps;
--   2. its report consists of at most $c$ well-formed cover changes;
--   3. the maintained cover $C_t$ covers $A_t$;
--   4. if $A_t\neq\emptyset$,
--   $$\sum_{S\in C_t}c_0(S)\le2048\,(1+\ln\Delta_t)\,\mathrm{OPT}_0(A_t),\qquad\Delta_t=\max_{S\in\mathcal F}|S\cap A_t|;$$
--   5. if $A_t=\emptyset$, the maintained cover is empty.
--
--   This is the paper's sharpest form of the main result: Theorem 1.2 follows from it with $\Delta_t\le n_t\le n$.
--
--   **Formalization Note** The input is the instance encoding followed by one word per update; time, report and maintained cover are measured between consecutive reads.
--
--   Differences from the source:
--   - generalization: a fixed family $\mathcal F$ of subsets of $U$ whose union is $U$ → an indexed family $(S_s)_{s<m}$ of subsets of $U$ with union $U$, in which two indices may carry the same subset; reason: the paper's family is an injectively indexed one; no step of the argument uses that the sets are distinct
--   - reading: a deterministic algorithm, with no machine model named in the statement → one program of the online word-RAM of §7 (p.56): $W$-bit words, constant-time arithmetic, integer division, comparisons, bit operations and indirect table access, one step per instruction, for every word size $W\ge c(\log_2(K+2)+1)$; reason: the proof is Theorem 7.5, stated 'in the stated word-RAM model' of p.56, whose words hold addresses, cost exponents and $O(\log N)$-bit integers; a RAM program is deterministic
--   - encoding: the algorithm receives the set system and then the updates, and after each update returns its cover; update time; recourse (sets added to or removed from the cover per update) → the input is the word list: instance encoding of $K$ words, then one word per update ($2e$ insert, $2e+1$ delete); an update's time is the number of steps from its read to the next read; its report is the list of words written in between ($2s$ adds set $s$, $2s+1$ removes it), and its length is the recourse; $C_t$ is the effect of all words written before the next read; reason: reading one element in one word is the §7 model (a bit-by-bit input would cost $\Theta(\log|U|)$ steps per update); the report length is at least the number of sets added or removed
--   - reading: a fixed positive cost $c_0(S)$ → the costs reach the program as positive rationals $c_0(S_s)=\mathrm{num}(s)/\mathrm{den}(s)$, numerator and denominator in binary; reason: a word-RAM receives encoded numbers; §7 speaks of 'the original cost encodings' and 'the encoded size of the fixed set system' (p.65)
--   - encoding: $O(\cdot)$ bounds and 'polynomial time' → one constant $c$, chosen before the instance, the update sequence and the word size, with explicit bounds $c\cdot(\dots)$ and $c(\cdot)^c$; reason: standard; choosing $c$ first makes the bounds independent of the instance, in particular of the cost aspect ratio
--   - reading: the maintained cover $C_t$ → $C_t$ covers $A_t$ is stated as a clause; reason: in fully dynamic set cover the maintained subfamily 'covers all active elements' (p.1); the cost bound alone does not say so
-- source:
--   Paul, Solomon, Weighted Set Cover with Constant Worst-Case Recourse: From Exponential to Best-Known Update Time (STOC 2027 submission, preprint, sha256 a671756b983353737f48798343a4d176654843ba40cd482f54283402087c5cb0), Theorem 7.6, p.66 (PDF 68)

import Mathlib
import Definitions.Def_DynSetCover_Protocol

namespace DynSetCover

/-- **Theorem 7.6** (Paul, Solomon, STOC 2027 submission, sha256 a671756b…, p.66 (PDF 68)).
After polynomial preprocessing of the fixed input set system, the algorithm can process update
`t` in `O(f log(n_t + 2))` worst-case time with `O(1)` worst-case recourse, without an advance
bound on the active-set size. For every nonempty `A_t`, the maintained cover `C_t` satisfies
`Σ_{S∈C_t} c0(S) ≤ 2048(1 + ln Δ_t) OPT0(A_t)`, `Δ_t = max_{S∈F} |S ∩ A_t|`. If `A_t = ∅`, the
maintained cover is empty.

There are one program `P` and one constant `c` such that for every instance, every valid update
sequence (of any length, with no bound on `|A_t|` given to the program) and every word size
`W ≥ c(log₂(K + 2) + 1)` (`K` the length of the instance encoding): every read of the input is
reached; preprocessing takes at most `c(K + 2)^c` steps; and for every update `t`, its time is
at most `c·f·log₂(n_t + 2)` steps, its report has at most `c` well-formed words, the maintained
cover `C_t` covers `A_t`, satisfies the displayed bound when `A_t ≠ ∅`, and is empty when
`A_t = ∅`.

**Formalization Note.** The machine is the online word-RAM `DRAM` (§7, p.56). The input is
`input inst num den σ`: the instance encoding (`K` words), then one word per update, so update `t` is
read by read number `K + t`; its time is the number of steps from that read to the next; its
report is the words written in between; `C_t` is the effect of all words written before the
next read. `K` here is the encoding length, not the paper's §7.5 element count. -/
theorem theorem_7_6 :
    ∃ (P : Program) (c : ℕ), ∀ (inst : Instance) (num den : Fin inst.m → ℕ), RatCosts inst num den →
      ∀ σ : List (Upd inst.u), Valid σ →
      ∀ W : ℕ, c * (Nat.log 2 ((enc inst num den).length + 2) + 1) ≤ W →
      let K := (enc inst num den).length
      let inp := input inst num den σ
      ∃ τ : ℕ → ℕ,
        (∀ k, 1 ≤ k → k ≤ K + σ.length + 1 → ReadsAt W P inp k (τ k)) ∧
        τ (K + 1) ≤ c * (K + 2) ^ c ∧
        ∀ t, 1 ≤ t → t ≤ σ.length →
          τ (K + t + 1) - τ (K + t) ≤ c * inst.freq * Nat.log 2 ((active σ t).card + 2) ∧
          (report W P inp τ (K + t)).length ≤ c ∧
          WellFormed inst.m (report W P inp τ (K + t)) ∧
          inst.Covers (coverAfter inst.m W P inp τ (K + t)) (active σ t) ∧
          ((active σ t).Nonempty →
            inst.cost0 (coverAfter inst.m W P inp τ (K + t)) ≤
              2048 * (1 + Real.log (inst.maxLoad (active σ t) : ℝ)) *
                inst.OPT0 (active σ t)) ∧
          (active σ t = ∅ → coverAfter inst.m W P inp τ (K + t) = ∅) := by sorry

end DynSetCover
