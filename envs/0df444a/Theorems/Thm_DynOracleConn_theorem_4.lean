-- Prove2me | Theorems.Thm_DynOracleConn_theorem_4
-- name    : DynOracleConn.theorem_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:52:13.784392+00:00
-- url     : https://prove2.me/theorems/530ccf09-e485-48bb-b59c-7eebf3810458
-- title:
--   Theorem 4, p.7 — fully dynamic $s$–$t$ connectivity with $B$ bits needs $\Omega(n^2/B)$ amortized matrix probes and $\Omega(n/B)$ list probes, even on forests
-- statement:
--   There are constants $\eta,c>0$ (and $\kappa_1,\kappa_2>0$) such that the following holds for all $n$, all $1\le B\le\eta n$, all real $T$ and all terminals $s\ne t$ in $[n]$, and for every randomized algorithm with at most $2^B$ persistent states.
--
--   1. **Matrix model.** If the algorithm's expected amortized number of adjacency probes per update is at most $T$ and
--
--      $$BT\le cn^2,$$
--
--      then there is a valid update sequence $\sigma$ with $\kappa_1n\le|\sigma|\le\kappa_2n$ that keeps the graph a forest at every prefix, on which
--
--      $$\mathbb P[\text{every answer is correct}]<\frac23.$$
--
--   2. **List model.** The same holds with the same constants for adjacency-list probes and $BT\le cn$.
--
--   Each update's probes see the graph before the update, and each answer is checked against the graph after it. This is the paper's main lower bound. It implies that amortized $\Omega(n^2/B)$ matrix probes and $\Omega(n/B)$ list probes are necessary, even on sequences of length $\Theta(n)$ on forests.
--
--   **Formalization Note** Randomness is a probability space of deterministic algorithms with measurable runs. Memory inside one update is not limited, the step may depend on the update index, and expected cost is only required on valid forest sequences. These enlarge the class of algorithms, so the bound is stronger than the printed one.
--
--   Differences from the source:
--   - generalization: at most B bits of memory, counting temporary storage → at most 2^B persistent states; memory inside an update is unlimited; the step may depend on the update index; reason: every algorithm of the paper's model lies in this class, and §3 p.19 says the proof allows it
--   - generalization: a randomized algorithm reading independent uniform random words → a probability space of deterministic algorithms; the tape is not charged; reason: random tapes are one such space; the proof fixes the tape (p.26)
--   - generalization: at most T probes per update (amortized) → expected total cost at most |σ|T, on valid forest sequences only; reason: worst-case amortized implies this; p.26 covers the expected version, and the proof only uses forest sequences
--   - generalization: the hard instance chooses its own s, t → every s ≠ t; reason: relabel the vertices; s = t is excluded because a constant answer is then correct
--   - generalization: list model: neighbors in an arbitrary order → increasing order; reason: an algorithm for arbitrary orders works in particular for this one, so the bound for this order gives the printed one
--   - reading: B ≤ ηn, with B = 0 not excluded → 1 ≤ B; reason: in the paper B = Θ(S log n) with S ≥ 1 (p.6) and p.20 divides by B; at B = 0 the model above is false, since reading all n² pairs in each update is correct with BT = 0 (proved in the sanity file)
--   - encoding: randomized algorithm → measurable runs as a hypothesis; reason: a nondegeneracy condition: without it the event of correctness need not be measurable, and a partition of [0,1] into sets of full outer measure gives a false statement
--   - encoding: length Θ(n) → κ₁n ≤ |σ| ≤ κ₂n with κ₁, κ₂ chosen with η, c; reason: the definition of Θ with constants independent of n, B and the algorithm
--   - encoding: B bits of memory; [n]; Neighbor(v, j) undefined outside [d(v)] → Fintype.card S ≤ 2^B; Fin n; returns 0; reason: Lean conventions; same instances
-- source:
--   Aryanfard, Henzinger, Kuszmaul, Nogler, Vassilevska Williams, Connectivity in a New Bounded-Space Dynamic Model, STOC 2027 submission (manuscript sha256 e9b19480…), Theorem 4, p.7 (restated pp.18, 26)

import Mathlib
import Definitions.Def_DynOracleConn_Oracles
import Definitions.Def_DynOracleConn_RandAlg

namespace DynOracleConn

/-- **Theorem 4, p.7 (fully dynamic amortized lower bound).** Aryanfard, Henzinger, Kuszmaul, Nogler, Vassilevska Williams, *Connectivity in a New Bounded-Space
Dynamic Model*, STOC 2027 submission (manuscript sha256 e9b19480…), Theorem 4, p.7 (restated on
pp.18 and 26): "There exist constants η, c > 0 such that for any randomized algorithm A that uses at
most B bits of memory and at most T adjacency probes per update (amortized) for Dynamic s-t
Connectivity in the fully dynamic setting, such that B ≤ ηn and BT ≤ cn², there exists an input
sequence σ of length Θ(n) such that the algorithm answers all queries correctly with probability
less than 2/3 and the graph is a forest throughout the entire stream. For the adjacency-list model,
the same lower bound holds for BT ≤ cn."

There are constants `η, c > 0` and `κ₁, κ₂ > 0` such that for all `n`, all `B` with `1 ≤ B ≤ ηn`, all
real `T`, all terminals `s ≠ t` in `Fin n` and every state type with at most `2^B` states:
1. (matrix model) every randomized algorithm with measurable runs and expected amortized cost at
   most `T` adjacency probes per update on forest sequences, with `BT ≤ cn²`, has a valid update
   sequence `σ` with `κ₁n ≤ |σ| ≤ κ₂n`, keeping the graph a forest throughout, on which it answers
   correctly after every update with probability less than `2/3`;
2. (list model) the same with list probes and `BT ≤ cn`.

The proof (p.26): "From the reduction stated in Section 3.1.2, Theorem 3.7 implies the following.
Indeed, the reduction turns an update sequence σ of length |σ| = Θ(d) = Θ(n) into an input of
Theorem 3.7 such that each adjacency probe of A is answered by at most one probe P_X(i, j), and A
is correct at all time steps only if correct_total holds; we choose c so small that BT ≤ cn² implies
4|σ|T ≤ c_Bc_Ld³/B. If A makes at most |σ|T probes on every execution, then L_total ≤ c_Bc_Ld³/B
always, and if it does so only in expectation, then P_A[L_total > c_Bc_Ld³/B] ≤ 1/4 by Markov's
inequality; in both cases, A is correct at all time steps with probability at most
1/3 + 1/4 < 2/3."

**Formalization Note.**
1. Memory: `B` bits of persistent state are a state type `S` with `Fintype.card S ≤ 2 ^ B`; the
   memory used inside one update is not limited, and the step may depend on the update index.
2. Randomness: a probability space of deterministic algorithms with measurable runs; the random
   tape is not charged as memory.
3. Cost: `ExpAmortized` bounds the expected total number of probes by `|σ|T` on every valid update
   sequence that keeps the graph a forest.
4. Snapshot semantics: an update's probes see the graph before it; answers are checked after it.
5. `Θ(n)` is `κ₁n ≤ |σ| ≤ κ₂n` with `κ₁, κ₂` fixed together with `η, c`; one `η, c, κ₁, κ₂` serve
   both clauses.
6. `1 ≤ B` is assumed: with `0` persistent bits and unlimited memory inside an update, reading all
   `n²` pairs every update answers correctly. -/
theorem theorem_4 :
    ∃ η c κ₁ κ₂ : ℝ, 0 < η ∧ 0 < c ∧ 0 < κ₁ ∧ 0 < κ₂ ∧
      ∀ (n B : ℕ) (T : ℝ), 1 ≤ B → (B : ℝ) ≤ η * n →
      ∀ s t : Fin n, s ≠ t →
      ∀ (S : Type) [Fintype S], Fintype.card S ≤ 2 ^ B →
        (∀ A : RandAlg n (Fin n × Fin n) Bool S, MeasurableRuns A matrixOracle →
          (B : ℝ) * T ≤ c * (n : ℝ) ^ 2 → ExpAmortized A matrixOracle T →
          ∃ σ : List (PunctSketch.Update n), PunctSketch.IsValidStream σ ∧ ForestThroughout σ ∧
            κ₁ * n ≤ σ.length ∧ (σ.length : ℝ) ≤ κ₂ * n ∧
            A.μ {ω | (A.alg ω).AllCorrect matrixOracle s t σ} < 2 / 3) ∧
        (∀ A : RandAlg n (ListQuery n) ℕ S, MeasurableRuns A listOracle →
          (B : ℝ) * T ≤ c * (n : ℝ) → ExpAmortized A listOracle T →
          ∃ σ : List (PunctSketch.Update n), PunctSketch.IsValidStream σ ∧ ForestThroughout σ ∧
            κ₁ * n ≤ σ.length ∧ (σ.length : ℝ) ≤ κ₂ * n ∧
            A.μ {ω | (A.alg ω).AllCorrect listOracle s t σ} < 2 / 3) := by sorry

end DynOracleConn
