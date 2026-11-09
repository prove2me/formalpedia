-- Prove2me | Theorems.Thm_CodedSorting_lemma_7_2
-- name    : CodedSorting.lemma_7_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T23:07:37.291754+00:00
-- url     : https://prove2.me/theorems/f5c27dd2-62ca-4823-bce1-ab18c44d119f
-- title:
--   Lemma 7.2 — local sorting of $n\le M^2$ records in $O(1+\frac nB[1+(\log M/a)^{\tau}])$ block transfers
-- statement:
--   Let $N\ge2$ be the global input size, $B\ge1$, $2B\le M\le N$, $w=\Theta(\log N)$, and let records consist of a fixed number $r\ge1$ of words compared lexicographically. For $1\le n\le M^2$, an array of $n$ records can be sorted in
--   $$O\Big(1+\frac nB\Big[1+\Big(\frac{\log M}{a}\Big)^{\tau}\Big]\Big)\tag{19}$$
--   block transfers, $a=\log_2(M/B)$, $\tau=1-\varepsilon$, $\varepsilon=3/200000$, using at most $M$ words of memory and polynomial disk space.
--
--   The local sorter is the inner loop of the radix sort of §8: it forms the buckets of every partition step (Lemma 8.1) and sorts the small buckets.
--
--   **Formalization Note** Record $i$ occupies disk words $ir,\dots,ir+r-1$, and the sorted records are written back to the same words. The constants $C,k$ may depend on $r$.
--
--   Differences from the source:
--   - reading: the external-memory model of §3.1 (p.4) and Appendix D (p.39), described in prose → words `Fin (2^w)`, memory `Fin M → Word w`, disk `ℕ → Word w` with aligned blocks of $B$ words; each step applies an arbitrary memory map and one action (read a block into memory words $[o,o+B)$, write such a range to a block, nothing, or halt); every read and write is one block transfer; the step index $t$ is visible to every program; reason: the paper fixes no formal machine and this is its stated model; the step index carries no input data (every run is at step $t$ at time $t$) and is the only state Appendix D places outside the $M$ words; the program is chosen after $(N,M,B,w)$ and before the input, as p.4 says
--   - reading: $w=\Theta(\log N)$, with $O(\cdot)$ and polynomial-space constants independent of $N,M,B$ → for all $c_1>0$ and $c_2$ there are $C,k$ such that every instance with $c_1\log_2 N\le w\le c_2\log_2 N$ satisfies the bounds; reason: the hidden constants may depend on the $\Theta$-constants and on nothing else (Appendix D, p.39: "The threshold depends only on the construction and the constants in $w=\Theta(\log N)$"); this is the strongest reading
--   - reading: input, output and intermediate data on disk occupy $O(N^k)$ words → every disk block touched by a read or write lies below word $C\cdot N^k$; reason: only transferred blocks can be read or changed, and the input lies in words $0,\dots,N-1$
--   - reading: "records": an input integer, possibly tagged, or "a constant number of integer fields compared lexicographically" (p.26) → for every fixed $r\ge1$, records of $r$ words in lexicographic order, $C,k$ depending on $r$; reason: the stronger of the paper's readings; $r=1$ is the word case
--   - encoding: an array of $n$ records on disk → record $i$ in disk words $[ir,ir+r)$, rest of disk and memory $0$; output in the same words; reason: contiguous storage
--   - reading: the main-text proof assumes $M$ and $M/B$ larger than fixed constants; Corollary A.3 (p.36) extends the result → every $2B\le M\le N$, $B\ge1$, $N\ge2$, with no size threshold; reason: Corollary A.3 states the bound for every $2B\le M$; $M\le N$ and $N\ge2$ are the standing assumptions of §3.1
--   - encoding: $O(\cdot)$ bound → a single constant $C$ multiplying the expression; reason: the expression is at least $1$ under the hypotheses, so this is the meaning of $O(\cdot)$
--   - encoding: the algorithm sorts → there is a step $T$ at which the run has halted; reason: halting is implicit in "sorted"; no time bound is stated or added
-- source:
--   B. Li, Z. Li, S. Liu, Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting, arXiv:2610.20079 (held version, sha256 6e149d97…8850b), Lemma 7.2, p.28 (PDF 29), with the record convention of §7, p.26 (PDF 27)

import Mathlib
import Definitions.Def_CodedSorting_Machine
import Definitions.Def_CodedSorting_Records
import Definitions.Def_CodedSorting_Exponent

namespace CodedSorting

/-- **Lemma 7.2 (Local sorting)**, arXiv:2610.20079 (held version, sha256 6e149d97…8850b), p.28.

For `1 ≤ n ≤ M²`, an array containing `n` records can be sorted in
`O(1 + (n/B) [1 + (log M / a)^τ])` block transfers, `a = log(M/B)`, `τ = 1 − ε`, `ε = 3/200000`,
using at most `M` words of memory and polynomial disk space.

**Formalization Note.** A record is `r` machine words compared lexicographically ("A record may
also consist of a constant number of integer fields compared lexicographically", p.26), for every
fixed `r ≥ 1`; `C, k` may depend on `r`. Record `i` is in disk words `[i·r, i·r + r)`, the rest of
the disk is `0`, and the sorted records are written back to the same words. `N` is the global
input size: `w = Θ(log N)`, `2B ≤ M ≤ N` (§3.1, p.4) and the disk is polynomial in `N`. The machine
and quantifier order are those of `theorem_3_1`. The range is every `2B ≤ M` (Corollary A.3,
p.36). -/
theorem lemma_7_2 :
    ∀ r : ℕ, 1 ≤ r → ∀ c₁ c₂ : ℝ, 0 < c₁ → ∃ C : ℝ, ∃ k : ℕ,
      ∀ N M B w n : ℕ, 2 ≤ N → 1 ≤ B → 2 * B ≤ M → M ≤ N →
        c₁ * Real.logb 2 N ≤ w → (w : ℝ) ≤ c₂ * Real.logb 2 N → 1 ≤ n → n ≤ M ^ 2 →
        ∃ P : Program M B w, ∀ x : Fin n → Record r w, ∃ T : ℕ,
          (run P T (initCfgOf (M := M) (recordDisk x))).halted = true ∧
          IsSortedRecords x (run P T (initCfgOf (M := M) (recordDisk x))).disk ∧
          ((run P T (initCfgOf (M := M) (recordDisk x))).ios : ℝ) ≤
            C * (1 + (n : ℝ) / B * (1 + (Real.logb 2 M / Real.logb 2 ((M : ℝ) / B)) ^ tau)) ∧
          ((run P T (initCfgOf (M := M) (recordDisk x))).maxEnd : ℝ) ≤ C * (N : ℝ) ^ k := by sorry

end CodedSorting
