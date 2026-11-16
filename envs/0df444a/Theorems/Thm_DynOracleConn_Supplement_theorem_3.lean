-- Prove2me | Theorems.Thm_DynOracleConn_Supplement_theorem_3
-- name    : DynOracleConn.Supplement.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T22:47:41.723621+00:00
-- url     : https://prove2.me/theorems/898d0716-bea1-4935-9c49-223c1fb41723
-- title:
--   Theorem 3, p.27 — incremental list model with $B\le\eta n$ bits: worst-case $\tilde\Omega(n^2/B^2)$ probes per update on $\Theta(n^2/B)$ insertions
-- statement:
--   There are constants $\eta,C,\kappa_1,\kappa_2>0$ and $k,n_0\in\mathbb N$ such that the following holds for all $n\ge n_0$, all $B$ with $1\le B\le\eta n$, all real $T$, all terminals $s\ne t$ in $[n]$, and every randomized algorithm for incremental dynamic $s$–$t$ connectivity in the adjacency-list model with at most $2^B$ persistent states. Call an insertion-only sequence **admissible** if its length lies in $[\kappa_1n^2/B,\ \kappa_2n^2/B]$. Suppose that for every ordering of the adjacency lists the following two conditions hold.
--
--   1. On every admissible sequence, the algorithm answers correctly after every update with probability at least $3/4$.
--   2. On every execution and every admissible sequence, each update makes at most $T$ list probes.
--
--   Then
--
--   $$T\ \ge\ \frac{C\,n^2}{B^2\,(\log_2 n)^k}.$$
--
--   The hard sequences have $\Theta(n^2/B)$ insertions; they build $\Theta(B)$ cliques of size $\Theta(n/B)$. The bound matches the worst-case time of the Metropolis-walk algorithm of Theorem 1(b) up to polylogarithmic factors.
--
--   **Formalization Note** An ordering is a key $\rho_v$ per vertex, fixed for the whole sequence, and the lists are sorted by it. Each update's probes see the graph before it, and the answer is checked against the graph after it. Time is counted in oracle probes. Memory inside an update is not limited and the step may depend on the update index.
--
--   Differences from the source:
--   - generalization: adjacency lists in an arbitrary (adversarial) order (pp.4, 30): the algorithm must be correct for every ordering → the hypotheses are required only for orderings fixed over the whole sequence (one key per vertex); reason: a weaker hypothesis; the proof uses one such ordering (lexicographic by reversed label, s and t last, p.30)
--   - reading: "on sequences of Θ(n²/B) insertions" → the success and probe hypotheses only on insertion-only sequences of length in [κ₁n²/B, κ₂n²/B], with κ₁, κ₂ fixed with η; reason: the definition of Θ; the hard sequences (the graph G of §5.1 plus one insertion) have this length
--   - encoding: time Ω̃(n²/B²) → T ≥ C·n²/(B²·(log₂ n)^k) for n ≥ n₀; reason: Ω̃ suppresses factors polynomial in log n (footnote 1, p.1)
--   - generalization: B bits of working memory (counting temporary storage) → a persistent state type with at most 2^B elements; memory inside an update is unlimited; the step may depend on the update index; reason: the base model of Theorem 4; it contains every B-bit algorithm of the paper, so a lower bound for it implies the printed one
--   - generalization: a randomized algorithm reading independent uniform random words → a probability space of deterministic algorithms; the tape is not charged as memory; reason: random tapes are one such space
--   - encoding: probabilities over the algorithm's randomness → measurable runs as a hypothesis; reason: a nondegeneracy condition: it makes the probability of correctness well defined on a general probability space
--   - encoding: worst-case time per update, on every execution (p.6) → at most T list probes at every update of every admissible sequence, for every outcome of the randomness; reason: p.4: the lower bounds are proved for the number of queries
--   - reading: B = Θ(S log n) bits, B = 0 not excluded → 1 ≤ B; reason: S ≥ 1 words gives B ≥ 1; the bound divides by B; at B = 0 the generalized model reads every pair in each update
--   - generalization: the algorithm's terminals s, t → every pair s ≠ t; reason: relabel the vertices of the hard instances; s = t is excluded because a constant answer is then correct
--   - encoding: [n]; B bits of state → Fin n; Fintype.card S ≤ 2^B; reason: Lean conventions; same instances
--   - encoding: Neighbor(v, j) undefined outside [d(v)] → returns 0; reason: Lean convention; it carries no information beyond d(v)
-- source:
--   Aryanfard, Henzinger, Kuszmaul, Nogler, Vassilevska Williams, Connectivity in a New Bounded-Space Dynamic Model, STOC 2027 submission (manuscript sha256 e9b19480…), Theorem 3, p.27 (also p.6); §5.1, p.30

import Mathlib
import Definitions.Def_DynOracleConn_Supplement_Incremental

namespace DynOracleConn

namespace Supplement

/-- **Theorem 3, p.27 (worst-case lower bound, list model).** Aryanfard, Henzinger, Kuszmaul,
Nogler, Vassilevska Williams, *Connectivity in a New Bounded-Space Dynamic Model*, STOC 2027
submission (manuscript sha256 e9b19480…), Theorem 3, p.27 (also p.6): "There is a constant η > 0 such
that every randomized algorithm for Dynamic s-t Connectivity in the incremental setting and the list
model with B = Θ(S log n) ≤ ηn bits of working memory such that, for every update sequence, with
probability at least 3/4, all of its answers are correct, needs worst-case time Ω̃(n²/B²) per update,
on sequences of Θ(n²/B) insertions."

There are constants `η, C, κ₁, κ₂ > 0` and `k, n₀ ∈ ℕ` such that for all `n ≥ n₀`, all `B` with
`1 ≤ B ≤ ηn`, all real `T`, all terminals `s ≠ t` and every state type with at most `2^B` states: call
an insertion-only sequence *admissible* if its length lies in `[κ₁n²/B, κ₂n²/B]`. Every randomized
list-model algorithm that, for every ordering of the adjacency lists, has measurable runs, answers
correctly after every update of every admissible sequence with probability at least `3/4`, and makes
at most `T` list probes at every update of every admissible sequence on every execution, has
`T ≥ C·n² / (B²·(log₂ n)^k)`.

**Formalization Note.**
1. Base model as in Theorem 4: `B` bits of persistent state are a state type with at most `2^B`
   elements, unlimited memory inside an update, an index-dependent step, randomness a probability
   space of deterministic algorithms.
2. Orderings: the lists are "arbitrary (i.e., adversarial)" (§5.1, p.30); the algorithm must work for
   every ordering `ρ` of `listOracleBy` (lists sorted by a key `ρ v` per vertex), fixed for the whole
   sequence. The proof picks one such ordering.
3. "On sequences of Θ(n²/B) insertions": the hypotheses are only required on insertion-only sequences
   whose length lies in `[κ₁n²/B, κ₂n²/B]`, with `κ₁, κ₂` fixed with `η`.
4. `Ω̃` suppresses factors polynomial in `log n` (footnote 1, p.1): `C·n²/(B²·(log₂ n)^k)`. Time is
   counted in oracle probes (p.4), on every execution (p.6). -/
theorem theorem_3 :
    ∃ η C κ₁ κ₂ : ℝ, 0 < η ∧ 0 < C ∧ 0 < κ₁ ∧ 0 < κ₂ ∧ ∃ k n₀ : ℕ,
      ∀ (n B : ℕ) (T : ℝ), n₀ ≤ n → 1 ≤ B → (B : ℝ) ≤ η * n →
      ∀ s t : Fin n, s ≠ t →
      ∀ (S : Type) [Fintype S], Fintype.card S ≤ 2 ^ B →
      ∀ A : RandAlg n (ListQuery n) ℕ S,
        (∀ ρ : Fin n → Equiv.Perm (Fin n), MeasurableRuns A (listOracleBy ρ)) →
        (∀ (ρ : Fin n → Equiv.Perm (Fin n)) (σ : List (PunctSketch.Update n)), IsIncremental σ →
          κ₁ * (n : ℝ) ^ 2 / B ≤ σ.length → (σ.length : ℝ) ≤ κ₂ * (n : ℝ) ^ 2 / B →
          (3 / 4 : ENNReal) ≤ A.μ {ω | (A.alg ω).AllCorrect (listOracleBy ρ) s t σ}) →
        (∀ ρ : Fin n → Equiv.Perm (Fin n), WorstCaseOn A (listOracleBy ρ)
          (fun σ => IsIncremental σ ∧ κ₁ * (n : ℝ) ^ 2 / B ≤ σ.length ∧
            (σ.length : ℝ) ≤ κ₂ * (n : ℝ) ^ 2 / B) T) →
        C * (n : ℝ) ^ 2 / ((B : ℝ) ^ 2 * Real.logb 2 n ^ k) ≤ T := by sorry

end Supplement

end DynOracleConn
