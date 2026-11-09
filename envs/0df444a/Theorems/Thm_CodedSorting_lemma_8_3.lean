-- Prove2me | Theorems.Thm_CodedSorting_lemma_8_3
-- name    : CodedSorting.lemma_8_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T23:06:54.843044+00:00
-- url     : https://prove2.me/theorems/1722d5bb-25ba-46ba-aed9-9102edf1081d
-- title:
--   Lemma 8.3 — sorting $N$ integers in $O(N)$ block transfers for every $M\ge 2B$
-- statement:
--   Let $N\ge2$, $B\ge1$, $2B\le M\le N$ and $w=\Theta(\log N)$. An array of $N$ integers of $w$ bits can be sorted in $O(N)$ block transfers, using at most $M$ words of memory and polynomial disk space.
--
--   This covers memory sizes below the fixed threshold of the main construction, where $B$ is bounded and $O(N)=O(N/B)$.
--
--   **Formalization Note** When $w<\lceil\log_2N\rceil$ the paper's counting sort uses the predetermined step index outside memory (p.32, Appendix D); the machine gives every program its step index.
--
--   Differences from the source:
--   - reading: the external-memory model of §3.1 (p.4) and Appendix D (p.39), described in prose → words `Fin (2^w)`, memory `Fin M → Word w`, disk `ℕ → Word w` with aligned blocks of $B$ words; each step applies an arbitrary memory map and one action (read a block into memory words $[o,o+B)$, write such a range to a block, nothing, or halt); every read and write is one block transfer; the step index $t$ is visible to every program; reason: the paper fixes no formal machine and this is its stated model; the step index carries no input data (every run is at step $t$ at time $t$) and is the only state Appendix D places outside the $M$ words; the program is chosen after $(N,M,B,w)$ and before the input, as p.4 says
--   - reading: $w=\Theta(\log N)$, with $O(\cdot)$ and polynomial-space constants independent of $N,M,B$ → for all $c_1>0$ and $c_2$ there are $C,k$ such that every instance with $c_1\log_2 N\le w\le c_2\log_2 N$ satisfies the bounds; reason: the hidden constants may depend on the $\Theta$-constants and on nothing else (Appendix D, p.39: "The threshold depends only on the construction and the constants in $w=\Theta(\log N)$"); this is the strongest reading
--   - reading: input, output and intermediate data on disk occupy $O(N^k)$ words → every disk block touched by a read or write lies below word $C\cdot N^k$; reason: only transferred blocks can be read or changed, and the input lies in words $0,\dots,N-1$
--   - reading: the integers are on disk and are written back in nondecreasing order → the input occupies disk words $0,\dots,N-1$ (the rest of the disk and the memory are $0$), and at the halt the same words hold a nondecreasing permutation of the input (repeated values allowed); reason: the paper does not fix the disk positions; using the input words for the output is the natural reading and costs at most one extra scan
--   - encoding: integers of $w$ bits → `Fin (2^w)`, ordered as integers; reason: unsigned $w$-bit words; same instances
--   - encoding: $O(\cdot)$ bound → a single constant $C$ multiplying the expression; reason: the expression is at least $1$ under the hypotheses, so this is the meaning of $O(\cdot)$
--   - encoding: the algorithm sorts → there is a step $T$ at which the run has halted; reason: halting is implicit in "sorted"; no time bound is stated or added
--   - reading: "For every $M\ge 2B$" → $2B\le M\le N$, $B\ge1$, $N\ge2$; reason: $M\le N$ and $N\ge2$ are the standing assumptions of §3.1 (p.4: "$2B\le M\le N$"), under which §8 works
-- source:
--   B. Li, Z. Li, S. Liu, Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting, arXiv:2610.20079 (held version, sha256 6e149d97…8850b), Lemma 8.3, p.31 (PDF 32)

import Mathlib
import Definitions.Def_CodedSorting_Machine

namespace CodedSorting

/-- **Lemma 8.3 (A linear number of individual record accesses)**, arXiv:2610.20079 (held version, sha256 6e149d97…8850b), p.31.

For every `M ≥ 2B`, an array of `N` integers of `w = Θ(log N)` bits can be sorted in `O(N)` block
transfers, using at most `M` words of memory and polynomial disk space.

**Formalization Note.** The machine, the input and output conventions, the order of quantifiers
and the reading of `w = Θ(log N)` and polynomial disk space are those of `theorem_3_1`; the
standing range `2B ≤ M ≤ N` of §3.1 (p.4) is kept. The proof's case `w < ⌈log N⌉` uses the step
index outside memory (p.32, Appendix D), which the machine provides to every program. -/
theorem lemma_8_3 :
    ∀ c₁ c₂ : ℝ, 0 < c₁ → ∃ C : ℝ, ∃ k : ℕ,
      ∀ N M B w : ℕ, 2 ≤ N → 1 ≤ B → 2 * B ≤ M → M ≤ N →
        c₁ * Real.logb 2 N ≤ w → (w : ℝ) ≤ c₂ * Real.logb 2 N →
        ∃ P : Program M B w, ∀ x : Fin N → Word w, ∃ T : ℕ,
          (run P T (initCfg (M := M) x)).halted = true ∧
          IsSortedOutput x (run P T (initCfg (M := M) x)).disk ∧
          ((run P T (initCfg (M := M) x)).ios : ℝ) ≤ C * N ∧
          ((run P T (initCfg (M := M) x)).maxEnd : ℝ) ≤ C * (N : ℝ) ^ k := by sorry

end CodedSorting
