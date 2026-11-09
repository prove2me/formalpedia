-- Prove2me | Theorems.Thm_CodedSorting_proposition_8_2
-- name    : CodedSorting.proposition_8_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T23:07:07.156189+00:00
-- url     : https://prove2.me/theorems/2fde2211-8b42-4d29-a1e7-3cefe86c7784
-- title:
--   Proposition 8.2 — sorting $N\ge M^2$ integers in $O(\frac NB[1+\frac{p}{a^{\tau}h^{\varepsilon}}])$ block transfers
-- statement:
--   Let $B\ge1$, $2B\le M$, $N\ge M^2$ and $w=\Theta(\log N)$. The $N$ input integers of $w$ bits can be sorted in
--   $$O\Big(\frac NB\Big[1+\frac{p}{a^{\tau}h^{\varepsilon}}\Big]\Big)$$
--   block transfers, where $p=\log_2(N/M)$, $a=\log_2(M/B)$, $h=\log_2 M$, $\tau=1-\varepsilon$ and $\varepsilon=3/200000$, using at most $M$ words of memory and polynomial disk space.
--
--   This is the large-input case of Theorem 3.1: since $p\le\log N$, the bound is at most the bound (2).
--
--   Differences from the source:
--   - reading: the external-memory model of §3.1 (p.4) and Appendix D (p.39), described in prose → words `Fin (2^w)`, memory `Fin M → Word w`, disk `ℕ → Word w` with aligned blocks of $B$ words; each step applies an arbitrary memory map and one action (read a block into memory words $[o,o+B)$, write such a range to a block, nothing, or halt); every read and write is one block transfer; the step index $t$ is visible to every program; reason: the paper fixes no formal machine and this is its stated model; the step index carries no input data (every run is at step $t$ at time $t$) and is the only state Appendix D places outside the $M$ words; the program is chosen after $(N,M,B,w)$ and before the input, as p.4 says
--   - reading: $w=\Theta(\log N)$, with $O(\cdot)$ and polynomial-space constants independent of $N,M,B$ → for all $c_1>0$ and $c_2$ there are $C,k$ such that every instance with $c_1\log_2 N\le w\le c_2\log_2 N$ satisfies the bounds; reason: the hidden constants may depend on the $\Theta$-constants and on nothing else (Appendix D, p.39: "The threshold depends only on the construction and the constants in $w=\Theta(\log N)$"); this is the strongest reading
--   - reading: input, output and intermediate data on disk occupy $O(N^k)$ words → every disk block touched by a read or write lies below word $C\cdot N^k$; reason: only transferred blocks can be read or changed, and the input lies in words $0,\dots,N-1$
--   - reading: the integers are on disk and are written back in nondecreasing order → the input occupies disk words $0,\dots,N-1$ (the rest of the disk and the memory are $0$), and at the halt the same words hold a nondecreasing permutation of the input (repeated values allowed); reason: the paper does not fix the disk positions; using the input words for the output is the natural reading and costs at most one extra scan
--   - encoding: integers of $w$ bits → `Fin (2^w)`, ordered as integers; reason: unsigned $w$-bit words; same instances
--   - encoding: $O(\cdot)$ bound → a single constant $C$ multiplying the expression; reason: the expression is at least $1$ under the hypotheses, so this is the meaning of $O(\cdot)$
--   - encoding: the algorithm sorts → there is a step $T$ at which the run has halted; reason: halting is implicit in "sorted"; no time bound is stated or added
--   - reading: the main-text proof assumes $M$ and $M/B$ larger than fixed constants; Corollary A.3 (p.36) extends the result → every $2B\le M\le N$, $B\ge1$, $N\ge2$, with no size threshold; reason: Corollary A.3 states the bound for every $2B\le M$; $M\le N$ and $N\ge2$ are the standing assumptions of §3.1
-- source:
--   B. Li, Z. Li, S. Liu, Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting, arXiv:2610.20079 (held version, sha256 6e149d97…8850b), Proposition 8.2, p.30 (PDF 31)

import Mathlib
import Definitions.Def_CodedSorting_Machine
import Definitions.Def_CodedSorting_Exponent

namespace CodedSorting

/-- **Proposition 8.2 (Sorting large inputs)**, arXiv:2610.20079 (held version, sha256 6e149d97…8850b), p.30.

For `N ≥ M²`, the `N` input integers can be sorted in `O((N/B) [1 + p/(a^τ h^ε)])` block transfers,
with `p = log(N/M)`, `a = log(M/B)`, `h = log M`, `τ = 1 − ε`, `ε = 3/200000`, using at most `M`
words of memory and polynomial disk space.

**Formalization Note.** The machine, the input and output conventions, the order of quantifiers
and the reading of `w = Θ(log N)` and polynomial disk space are those of `theorem_3_1`. The range
is every `2B ≤ M ≤ N` with `M² ≤ N`: the main-text proof assumes `M` and `M/B` large and
Corollary A.3 (p.36) extends it to all `2B ≤ M`. -/
theorem proposition_8_2 :
    ∀ c₁ c₂ : ℝ, 0 < c₁ → ∃ C : ℝ, ∃ k : ℕ,
      ∀ N M B w : ℕ, 2 ≤ N → 1 ≤ B → 2 * B ≤ M → M ≤ N → M ^ 2 ≤ N →
        c₁ * Real.logb 2 N ≤ w → (w : ℝ) ≤ c₂ * Real.logb 2 N →
        ∃ P : Program M B w, ∀ x : Fin N → Word w, ∃ T : ℕ,
          (run P T (initCfg (M := M) x)).halted = true ∧
          IsSortedOutput x (run P T (initCfg (M := M) x)).disk ∧
          ((run P T (initCfg (M := M) x)).ios : ℝ) ≤
            C * ((N : ℝ) / B) * (1 + Real.logb 2 ((N : ℝ) / M) /
              ((Real.logb 2 ((M : ℝ) / B)) ^ tau * (Real.logb 2 M) ^ eps)) ∧
          ((run P T (initCfg (M := M) x)).maxEnd : ℝ) ≤ C * (N : ℝ) ^ k := by sorry

end CodedSorting
