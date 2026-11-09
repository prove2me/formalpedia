-- Prove2me | Theorems.Thm_CodedSorting_theorem_3_1
-- name    : CodedSorting.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T23:07:06.116424+00:00
-- url     : https://prove2.me/theorems/12faeca2-c9ab-4d9b-9e31-38091956da2b
-- title:
--   Theorem 3.1 — external-memory integer sorting in $O(\frac{N}{B}[1+\frac{\log N}{\log^{1-\varepsilon}(M/B)\log^{\varepsilon}M}])$ block transfers, $\varepsilon=3/200000$
-- statement:
--   Let $\varepsilon=3/200000=1.5\times10^{-5}$. For every $N\ge2$, $B\ge1$ and $2B\le M\le N$, $N$ integers of $w=\Theta(\log N)$ bits can be sorted deterministically in the external-memory model in
--   $$O\Big(\frac NB\Big[1+\frac{\log N}{(\log(M/B))^{1-\varepsilon}(\log M)^{\varepsilon}}\Big]\Big)\tag{2}$$
--   block transfers, logarithms to base 2. The algorithm uses at most $M$ words of memory and polynomial disk space, and is correct on every input, including inputs with repeated values.
--
--   The classical comparison bound is $\Theta\big(\frac NB[1+\frac{\log(N/M)}{\log(M/B)}]\big)$; when $M/B$ is small relative to $M$ (for example $M=2B$, $N=B^2$) the bound (2) is asymptotically smaller, which answers the question of Aggarwal and Vitter (1988) whether integer sorting can beat the comparison bound in this model.
--
--   **Formalization Note** The program is chosen after $(N,M,B,w)$ and before the input. The constants $C,k$ of the bound and of the disk space are chosen after the $\Theta$-constants $c_1,c_2$ of $w$ and before $N,M,B,w$. The memory has exactly $M$ words by type, and the only state outside memory is the step index of Appendix D.
--
--   Differences from the source:
--   - reading: the external-memory model of §3.1 (p.4) and Appendix D (p.39), described in prose → words `Fin (2^w)`, memory `Fin M → Word w`, disk `ℕ → Word w` with aligned blocks of $B$ words; each step applies an arbitrary memory map and one action (read a block into memory words $[o,o+B)$, write such a range to a block, nothing, or halt); every read and write is one block transfer; the step index $t$ is visible to every program; reason: the paper fixes no formal machine and this is its stated model; the step index carries no input data (every run is at step $t$ at time $t$) and is the only state Appendix D places outside the $M$ words; the program is chosen after $(N,M,B,w)$ and before the input, as p.4 says
--   - reading: $w=\Theta(\log N)$, with $O(\cdot)$ and polynomial-space constants independent of $N,M,B$ → for all $c_1>0$ and $c_2$ there are $C,k$ such that every instance with $c_1\log_2 N\le w\le c_2\log_2 N$ satisfies the bounds; reason: the hidden constants may depend on the $\Theta$-constants and on nothing else (Appendix D, p.39: "The threshold depends only on the construction and the constants in $w=\Theta(\log N)$"); this is the strongest reading
--   - reading: input, output and intermediate data on disk occupy $O(N^k)$ words → every disk block touched by a read or write lies below word $C\cdot N^k$; reason: only transferred blocks can be read or changed, and the input lies in words $0,\dots,N-1$
--   - reading: the integers are on disk and are written back in nondecreasing order → the input occupies disk words $0,\dots,N-1$ (the rest of the disk and the memory are $0$), and at the halt the same words hold a nondecreasing permutation of the input (repeated values allowed); reason: the paper does not fix the disk positions; using the input words for the output is the natural reading and costs at most one extra scan
--   - encoding: integers of $w$ bits → `Fin (2^w)`, ordered as integers; reason: unsigned $w$-bit words; same instances
--   - encoding: $O(\cdot)$ bound → a single constant $C$ multiplying the expression; reason: the expression is at least $1$ under the hypotheses, so this is the meaning of $O(\cdot)$
--   - encoding: the algorithm sorts → there is a step $T$ at which the run has halted; reason: halting is implicit in "sorted"; no time bound is stated or added
--   - reading: "there is a constant $\varepsilon>0$" with "we take $\varepsilon=1.5\times10^{-5}$" (p.4) → $\varepsilon=3/200000$ exactly; reason: the paper fixes this value (also in Lemma B.1); the explicit value implies the existential
--   - reading: the main-text proof assumes $M$ and $M/B$ larger than fixed constants; Corollary A.3 (p.36) extends the result → every $2B\le M\le N$, $B\ge1$, $N\ge2$, with no size threshold; reason: Corollary A.3 states the bound for every $2B\le M$; $M\le N$ and $N\ge2$ are the standing assumptions of §3.1
-- source:
--   B. Li, Z. Li, S. Liu, Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting, arXiv:2610.20079 (held version, sha256 6e149d97…8850b), Theorem 3.1, p.4 (PDF 5)

import Mathlib
import Definitions.Def_CodedSorting_Machine
import Definitions.Def_CodedSorting_Exponent

namespace CodedSorting

/-- **Theorem 3.1 (External-memory integer sorting)**, B. Li, Z. Li, S. Liu, arXiv:2610.20079 (held version, sha256 6e149d97…8850b), p.4.

With `ε = 3/200000`: for all constants `0 < c₁` and `c₂` of `w = Θ(log N)` there are `C` and `k`
such that for all `N ≥ 2`, `B ≥ 1`, `2B ≤ M ≤ N` and `c₁ log N ≤ w ≤ c₂ log N`, one program of the
external-memory machine with `M` words of memory and blocks of `B` words sorts every input of `N`
`w`-bit integers: it halts with the input in nondecreasing order in disk words `0, …, N−1`, after
at most `C (N/B) (1 + log N / ((log(M/B))^{1−ε} (log M)^ε))` block transfers, touching only disk
words below `C N^k`.

**Formalization Note.** Logarithms are base 2 (p.4). The constants `C, k` are chosen after the
`Θ`-constants `c₁, c₂` and before `N, M, B, w`; the program is chosen after `(N, M, B, w)` and before
the input ("The program is fixed from the size parameters, independently of the input values",
p.4). Memory is `Fin M → Word w`, so "at most M words of memory" is in the type; the only state
outside memory is the step index (Appendix D, p.39). "Deterministic" is the type of `Program`;
"correct on every input" is `∀ x`, repeated values allowed. Integers of `w` bits are `Fin (2^w)`. -/
theorem theorem_3_1 :
    ∀ c₁ c₂ : ℝ, 0 < c₁ → ∃ C : ℝ, ∃ k : ℕ,
      ∀ N M B w : ℕ, 2 ≤ N → 1 ≤ B → 2 * B ≤ M → M ≤ N →
        c₁ * Real.logb 2 N ≤ w → (w : ℝ) ≤ c₂ * Real.logb 2 N →
        ∃ P : Program M B w, ∀ x : Fin N → Word w, ∃ T : ℕ,
          (run P T (initCfg (M := M) x)).halted = true ∧
          IsSortedOutput x (run P T (initCfg (M := M) x)).disk ∧
          ((run P T (initCfg (M := M) x)).ios : ℝ) ≤
            C * ((N : ℝ) / B) * (1 + Real.logb 2 N /
              ((Real.logb 2 ((M : ℝ) / B)) ^ (1 - eps) * (Real.logb 2 M) ^ eps)) ∧
          ((run P T (initCfg (M := M) x)).maxEnd : ℝ) ≤ C * (N : ℝ) ^ k := by sorry

end CodedSorting
