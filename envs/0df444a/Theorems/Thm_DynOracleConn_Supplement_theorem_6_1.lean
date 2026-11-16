-- Prove2me | Theorems.Thm_DynOracleConn_Supplement_theorem_6_1
-- name    : DynOracleConn.Supplement.theorem_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T22:48:27.236093+00:00
-- url     : https://prove2.me/theorems/0e5f0db8-3de0-4501-b6cf-24fe73ef7bf0
-- title:
--   Theorem 6.1, p.33 — a total budget below $cn^{5/2}/\sqrt B$ matrix probes (or $cn^{3/2}/\sqrt B$ list probes) on $\Theta(n)$ insertions gives success $<2/3$
-- statement:
--   There are constants $c,c_0,\kappa_1,\kappa_2>0$ and $n_0$ such that for every $n\ge n_0$ there is a length $m$ with $\kappa_1n\le m\le\kappa_2n$ for which the following holds for all $B$ with $1\le B\le c_0n$, all terminals $s\ne t$ in $[n]$, and every state set with at most $2^B$ elements.
--
--   1. **Matrix model.** Let $\mathcal A$ be a randomized adjacency-matrix algorithm whose total number of probes is at most $q$ on every execution and every insertion-only sequence of length $m$, where
--   $$q\ <\ \frac{c\,n^{5/2}}{\sqrt B}.$$
--   Then there is an insertion-only sequence $\sigma$ of length $m$ such that
--   $$\mathbb P\big[\mathcal A\text{ answers correctly after every update of }\sigma\big]\ <\ \frac23.$$
--   2. **List model.** For every ordering of the adjacency lists, the same holds for every randomized adjacency-list algorithm with $q<c\,n^{3/2}/\sqrt B$.
--
--   Dividing by $m=\Theta(n)$, success probability at least $2/3$ requires amortized $\Omega(n^{3/2}/\sqrt B)$ matrix probes and $\Omega(\sqrt{n/B})$ list probes per update. This is Theorem 6 of the introduction, in which the list-model bound follows from the matrix-model bound because one list probe can be simulated by $O(n)$ matrix probes.
--
--   **Formalization Note** The length $m$ depends only on $n$, as the hypothesis on the budget refers to it. The paper's sequences have $2(N-1)+2R$ insertions with $N=\lfloor n/2\rfloor$ and $R=\lfloor(N-1)/8\rfloor$. Memory inside an update is not limited, the step may depend on the update index, and each update's probes see the graph before it.
--
--   Differences from the source:
--   - reading: "a fixed sequence of m = Θ(n) insertions", with "the budget … on every input of length m" → one m per n with κ₁n ≤ m ≤ κ₂n, fixed before B, s, t and the algorithm; budget on every insertion-only sequence of length m; reason: the budget hypothesis refers to m, so m precedes the algorithm; the construction (p.34) gives m = 2(N − 1) + 2R, which depends on n alone
--   - reading: "B-bit adjacency matrix algorithm with total probe budget q_total" → for every real q < c·n^{5/2}/√B: total probes at most q on every outcome and every insertion-only sequence of length m; reason: the paper's budget is an upper bound on every execution on every input of length m
--   - generalization: the list-model consequence, for the lists in an arbitrary order → clause 2 for every fixed ordering ρ, with the same constants c, c₀, κ₁, κ₂; reason: an algorithm for every ordering works for each one; the row-scan simulation works for any fixed ordering
--   - generalization: B bits of working memory (counting temporary storage) → a persistent state type with at most 2^B elements; memory inside an update is unlimited; the step may depend on the update index; reason: the base model of Theorem 4; it contains every B-bit algorithm of the paper, so a lower bound for it implies the printed one
--   - generalization: a randomized algorithm reading independent uniform random words → a probability space of deterministic algorithms; the tape is not charged as memory; reason: random tapes are one such space
--   - encoding: probabilities over the algorithm's randomness → measurable runs as a hypothesis; reason: a nondegeneracy condition: it makes the probability of correctness well defined on a general probability space
--   - reading: B = Θ(S log n) bits, B = 0 not excluded → 1 ≤ B; reason: S ≥ 1 words gives B ≥ 1; the bound divides by B; at B = 0 the generalized model reads every pair in each update
--   - generalization: the algorithm's terminals s, t → every pair s ≠ t; reason: relabel the vertices of the hard instances; s = t is excluded because a constant answer is then correct
--   - encoding: [n]; B bits of state → Fin n; Fintype.card S ≤ 2^B; reason: Lean conventions; same instances
-- source:
--   Aryanfard, Henzinger, Kuszmaul, Nogler, Vassilevska Williams, Connectivity in a New Bounded-Space Dynamic Model, STOC 2027 submission (manuscript sha256 e9b19480…), Theorem 6.1, p.33 (restated p.41) and the paragraph after it; Theorem 6, p.8; §6.1, p.34

import Mathlib
import Definitions.Def_DynOracleConn_Supplement_Incremental

namespace DynOracleConn

namespace Supplement

/-- **Theorem 6.1, p.33 (incremental amortized lower bound).** Aryanfard, Henzinger, Kuszmaul,
Nogler, Vassilevska Williams, *Connectivity in a New Bounded-Space Dynamic Model*, STOC 2027
submission (manuscript sha256 e9b19480…), Theorem 6.1, p.33 (restated p.41; informal Theorem 6,
p.8): "There are absolute constants c, c0 > 0 such that for large enough n and B ≤ c0n, for every
B-bit adjacency matrix algorithm with total probe budget q_total < cn^{5/2}/√B there is a fixed
sequence of m = Θ(n) insertions on which the algorithm answers all queries correctly with probability
strictly less than 2/3. Since the budget is an upper bound on every execution on every input of
length m, success probability at least 2/3 requires amortized Ω(n^{3/2}/√B) probes." And, after it:
"Since an adjacency list probe can be simulated with O(n) probes in the adjacency matrix model, an
amortized lower bound of Ω(√(n/B)) probes holds for the adjacency list model."

There are constants `c, c₀, κ₁, κ₂ > 0` and `n₀` such that for every `n ≥ n₀` there is a length `m`
with `κ₁n ≤ m ≤ κ₂n` such that for all `B` with `1 ≤ B ≤ c₀n`, all terminals `s ≠ t` and every state
type with at most `2^B` states:
1. every randomized matrix-model algorithm with measurable runs whose total number of probes is at
   most `q < c·n^{5/2}/√B` on every execution and every insertion-only sequence of length `m` has an
   insertion-only sequence of length `m` on which it answers correctly after every update with
   probability strictly less than `2/3`;
2. the same holds for every ordering of the adjacency lists and every randomized list-model algorithm
   with `q < c·n^{3/2}/√B`.

**Formalization Note.**
1. Base model as in Theorem 4 (`B` bits of persistent state as at most `2^B` states, unlimited memory
   inside an update, an index-dependent step, randomness a probability space of deterministic
   algorithms with measurable runs).
2. The length `m` is fixed by `n` before `B`, the terminals and the algorithm, as the budget
   hypothesis refers to it; the paper's sequences have `m = 2(N − 1) + 2R` insertions with
   `N = ⌊n/2⌋`, `R = ⌊(N − 1)/8⌋` (p.34).
3. The list clause holds for every fixed ordering `ρ` of the adjacency lists (`listOracleBy`), and
   uses the same constants. The amortized form in the theorem's last sentence is the same statement
   divided by `m`. -/
theorem theorem_6_1 :
    ∃ c c₀ κ₁ κ₂ : ℝ, 0 < c ∧ 0 < c₀ ∧ 0 < κ₁ ∧ 0 < κ₂ ∧ ∃ n₀ : ℕ,
      ∀ n : ℕ, n₀ ≤ n → ∃ m : ℕ, κ₁ * n ≤ m ∧ (m : ℝ) ≤ κ₂ * n ∧
      ∀ B : ℕ, 1 ≤ B → (B : ℝ) ≤ c₀ * n →
      ∀ s t : Fin n, s ≠ t →
      ∀ (S : Type) [Fintype S], Fintype.card S ≤ 2 ^ B →
        (∀ A : RandAlg n (Fin n × Fin n) Bool S, MeasurableRuns A matrixOracle →
          ∀ q : ℝ, q < c * (n : ℝ) ^ (5 / 2 : ℝ) / Real.sqrt B →
          TotalBudgetOn A matrixOracle (fun σ => IsIncremental σ ∧ σ.length = m) q →
          ∃ σ : List (PunctSketch.Update n), IsIncremental σ ∧ σ.length = m ∧
            A.μ {ω | (A.alg ω).AllCorrect matrixOracle s t σ} < 2 / 3) ∧
        (∀ (ρ : Fin n → Equiv.Perm (Fin n)) (A : RandAlg n (ListQuery n) ℕ S),
          MeasurableRuns A (listOracleBy ρ) →
          ∀ q : ℝ, q < c * (n : ℝ) ^ (3 / 2 : ℝ) / Real.sqrt B →
          TotalBudgetOn A (listOracleBy ρ) (fun σ => IsIncremental σ ∧ σ.length = m) q →
          ∃ σ : List (PunctSketch.Update n), IsIncremental σ ∧ σ.length = m ∧
            A.μ {ω | (A.alg ω).AllCorrect (listOracleBy ρ) s t σ} < 2 / 3) := by sorry

end Supplement

end DynOracleConn
