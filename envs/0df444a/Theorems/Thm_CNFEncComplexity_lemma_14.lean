-- Prove2me | Theorems.Thm_CNFEncComplexity_lemma_14
-- name    : CNFEncComplexity.lemma_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:33:24.773519+00:00
-- url     : https://prove2.me/theorems/f66ee6dd-f5ce-4a65-bcd0-989db5d13346
-- title:
--   Lemma 14 — Teutsch's explicit expander
-- statement:
--   There are a constant $c$ and one deterministic polynomial-time neighbor function such that for every integer $k\ge0$ and every finite universe $L=\{0,\dots,N-1\}$ with $N\ge 2^k$, there is a bipartite graph $(L,R,E)$ with $R=\{0,\dots,r-1\}$, where the $i$-th neighbor of a left vertex $\ell$ is the output of the neighbor function on $(N,k,\ell,i)$, such that:
--
--   1. $|R|=r<2^{k+3}$;
--   2. every left vertex has at most $D(N)=c\,(\lfloor\log_2 N\rfloor+1)^c$ neighbors (no $i$-th neighbor for $i\ge D(N)$), a fixed polynomial in $\lg|L|$;
--   3. every $S\subseteq L$ with $|S|\le 2^k$ has $|N(S)|\ge|S|$.
--
--   The neighbor function runs in time polynomial in the length of $(N,k,\ell,i)$ written in binary, i.e. in $\lg|L|$ and $\lg d$ for $i<d$.
--
--   By Hall's theorem, the expansion property lets any set of at most $2^k$ universe elements be matched into distinct right vertices; Lemma 11 uses this as an explicit hash table.
--
--   **Formalization Note** A finite universe is identified with $\{0,\dots,N-1\}$, so its elements can be written in binary. One machine and one constant $c$ serve every $k$ and $N$. Repeated neighbors are allowed; they do not change $N(S)$. The proof is in [Teu14, Section 4], not in this paper.
--
--   Differences from the source:
--   - encoding: finite universe L with |L| ≥ 2^k → L = Fin N with 2^k ≤ N; reason: every finite set is in bijection with Fin |L|, and the computation clause needs its elements written in binary
--   - reading: left degree bounded by a fixed polynomial in lg |L| → ∃ c before k and N, nbr (N,k,ℓ,i) = none for i ≥ c·(⌊log₂ N⌋+1)^c; reason: a polynomial with nonnegative coefficients is bounded by c(x+1)^c; the +1 covers |L| = 1
--   - reading: its ith neighbor can be computed deterministically in time polynomial in lg |L| and lg d → TM2ComputableInPolyTime encNbrIn encOptNat nbr, inputs (N, k, ℓ, i) in binary, output none or the neighbor; reason: polynomial time is model-robust; Mathlib's TM2 is the platform's standard machine model, and polynomial in the stated quantity is polynomial in the input length of this encoding
--   - encoding: bipartite graph (L, R, E) → R = {0, …, r−1} and E = {(ℓ, ρ) : nbr (N, k, ℓ, i) = some ρ for some i}, the graph given by the neighbor function; reason: the lemma's computation clause describes the graph by its ith-neighbor function; repeated or missing (none) neighbor slots do not change E or N(S)
-- source:
--   Krapivin, Przybocki, Subercaseaux, The CNF Encoding Complexity of Boolean Functions, arXiv:2611.05614 (held version, sha256 97421ce1…), Lemma 14, pp.13–14 (PDF 14–15)

import Mathlib
import Definitions.Def_CNFEncComplexity_encWords
import Definitions.Def_CNFEncComplexity_encNbrIn

namespace CNFEncComplexity

/-- **Lemma 14 (Teutsch's expander lemma [Teu14, Section 4]).** Krapivin, Przybocki, Subercaseaux, *The CNF Encoding Complexity of Boolean Functions*, arXiv:2611.05614 (held version, sha256 97421ce1…), Lemma 14, pp.13–14 (PDF 14–15):
"For every integer k ⩾ 0 and finite universe L with |L| ⩾ 2^k, there is a bipartite graph (L, R, E)
with |R| < 2^{k+3}, left degree bounded by a fixed polynomial in lg |L|, and |N(S)| ⩾ |S| for every
S ⊆ L of size at most 2^k. For each left vertex, its ith neighbor can be computed deterministically in
time polynomial in lg |L| and lg d, where d is the maximum left degree."

There are a constant `c` (the fixed polynomial is `D(N) = c·(⌊lg N⌋ + 1)^c`) and one
polynomial-time neighbor function `nbr` such that for every `k` and `N ≥ 2^k`, with `L = Fin N`,
there is `r < 2^{k+3}` (with `R = {0, …, r − 1}`) such that, writing `nbr (N, k, ℓ, i)` for the
`i`-th neighbor of `ℓ` (`none` if there is none):
1. every left vertex has no neighbor of index `≥ D(N)` (left degree `≤ D(N)`);
2. every neighbor lies in `R`;
3. every `S ⊆ L` with `|S| ≤ 2^k` has `|N(S)| ≥ |S|`.

**Formalization Note.** A finite universe is identified with `Fin N` (any bijection), so its elements
can be written in binary. The machine receives `(N, k, ℓ, i)` in binary (`encNbrIn`) and outputs
`encOptNat`; one machine serves every `(N, k)`. The constant `c` is fixed before `k` and `N`.
Repeated neighbors are allowed; they do not change `N(S)`. The proof is in [Teu14], not in this
paper. -/
theorem lemma_14 :
    ∃ c : ℕ, ∃ nbr : ℕ × ℕ × ℕ × ℕ → Option ℕ,
      Nonempty (Turing.TM2ComputableInPolyTime encNbrIn encOptNat nbr) ∧
      ∀ k N : ℕ, 2 ^ k ≤ N → ∃ r : ℕ, r < 2 ^ (k + 3) ∧
        (∀ l < N, ∀ i : ℕ, c * (Nat.log 2 N + 1) ^ c ≤ i → nbr (N, k, l, i) = none) ∧
        (∀ l < N, ∀ i ρ : ℕ, nbr (N, k, l, i) = some ρ → ρ < r) ∧
        ∀ S : Finset (Fin N), S.card ≤ 2 ^ k →
          S.card ≤ (S.biUnion fun l => (Finset.range (c * (Nat.log 2 N + 1) ^ c)).biUnion
            fun i => (nbr (N, k, (l : ℕ), i)).toFinset).card := by sorry

end CNFEncComplexity
