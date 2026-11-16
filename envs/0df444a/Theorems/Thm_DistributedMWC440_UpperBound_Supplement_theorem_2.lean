-- Prove2me | Theorems.Thm_DistributedMWC440_UpperBound_Supplement_theorem_2
-- name    : DistributedMWC440.UpperBound.Supplement.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:52:02.000538+00:00
-- url     : https://prove2.me/theorems/af9b0ba0-abee-45a1-8ad4-de91a682e15a
-- title:
--   Theorem 2 (Lower bound) — conditional CONGEST lower bound
-- statement:
--   Assume the Erdős girth conjecture for the integer $k\ge1$. Let $\varepsilon(n)\ge n^{-c}$ for a constant $c>0$. Then any distributed algorithm that solves $(k+1-\varepsilon)$-Apx-MWC with high probability in the CONGEST model requires
--
--   $$
--   \widetilde\Omega\!\left(n^{\frac{k+1}{2k+1}}\right)
--   $$
--
--   rounds. This holds both for directed unweighted graphs and for undirected weighted graphs (positive integer weights bounded by a polynomial in $n$).
--
--   Precisely: for each $c>0$, message exponent $B$ and ID exponent $b\ge1$ there are constants $C>0$ and $p$ (and, for weighted graphs, a weight exponent $q$) such that, whenever an algorithm $A$ solves the problem with high probability within $T(n)$ rounds — for some $c'>0$ and all large $n$, on every network of size $n$ it halts by round $T(n)$ with messages below $\max(2,n)^B$ and a correct output with probability at least $1-n^{-c'}$ — then $T(n)\ge C\,n^{(k+1)/(2k+1)}/(\log n)^p$ for all sufficiently large $n$.
--
--   Together with Theorem 1 (applied to $(k+1-\varepsilon)$-approximation), this shows that $\widetilde\Theta(n^{(k+1)/(2k+1)}+D)$ is the round complexity of $(k+1-\varepsilon)$-Apx-MWC for every integer $k\ge2$, conditional on the conjecture.
--
--   Differences from the source:
--   - generalization: assuming the Erdős girth conjecture (for all k) → the hypothesis ErdosGirth k for the single integer k of the statement; reason: it assumes less; the conjecture for every k gives it
--   - reading: Conjecture 1.2: for all n ≥ 1 a bipartite graph with |E| ∈ Ω(n^(1+1/k)) and girth > 2k → ∃ c > 0, ∃ n₀, ∀ n ≥ n₀, a bipartite simple graph on exactly n vertices with at least c·n^(1+1/k) edges and girth > 2k; reason: the vertex count must be n and Ω is asymptotic; read literally for n = 1 the conjecture is false (one vertex, no edge), which would make the theorem vacuous
--   - generalization: any distributed algorithm in the CONGEST model (a node initially knows its ID and its incident weights) → any n-dependent state machine that knows n, its ID and, per port, the neighbour's ID and the edge label (weight or arc directions), with the message width required only on successful executions; reason: a larger class than the source's; it contains every base-mission CONGEST protocol with an identical execution, so the bound implies the source's
--   - encoding: ε ∈ n^(−O(1)) → for an exponent c > 0, every ε : ℕ → ℝ with n^(−c) ≤ ε(n) for all n; the constants depend on c but not on ε; reason: spells out the polynomial lower bound on ε
--   - encoding: (k + 1 − ε)-Apx-MWC, defined by Definition 1.1 only for ratio ≥ 1 (ε ≤ k) → no upper bound on ε; for ε(n) > k the ratio is below 1 (or negative), no correct cycle output exists on an input with a cycle, so the w.h.p. hypothesis fails and the clause is vacuous there; reason: totalizes the ratios Definition 1.1 leaves undefined without changing any instance with ratio ≥ 1
--   - encoding: requires Ω̃(n^((k+1)/(2k+1))) rounds → constants C > 0 and p chosen before the algorithm (after c, B, b) such that T(n) ≥ C·n^((k+1)/(2k+1))/(log n)^p for all n ≥ n₀, with n₀ depending on the algorithm; reason: spells out Ω̃ with polylogarithmic factors and uniform constants
--   - reading: a lower bound on the number of rounds → the bound for all sufficiently large n, not only for infinitely many n; reason: the stronger reading of 'requires'
--   - encoding: solves with high probability → ∃ c' > 0, ∃ n₁, ∀ n ≥ n₁, on every input of size n: with probability ≥ 1 − n^(−c') the algorithm halts by round T(n), all messages so far are below (max 2 n)^B, and the output is correct; reason: 1 − 1/poly(n), in the weakest form for a hypothesis
--   - encoding: O(log n)-bit messages and identifiers → for every message exponent B payloads below (max 2 n)^B; distinct IDs below (max 2 n)^b for an ID exponent b ≥ 1; reason: b ≥ 1 is needed for n distinct IDs; the base mission's convention
--   - encoding: undirected weighted graphs (positive integer weights in n^(O(1))) → positive integer weights at most n^q for a weight exponent q chosen before the algorithm (depending on k, c, B, b); reason: the source's rescaling w' = M·w + 1 needs weights polynomial in n with an exponent depending on c
--   - encoding: CONGEST networks → connected communication graphs (the underlying undirected graph of a digraph) with bidirectional links and private port orders; reason: the CONGEST model of §3
--   - encoding: directed unweighted graphs and the cycle output → loopless digraphs on Fin n (antiparallel arcs allowed); output the number of arcs of one common directed simple cycle and, at both endpoints of every link, one mark bit per arc; reason: Definition 1.1's output convention for directed cycles
--   - encoding: the minimum-cycle task where a cycle exists → OPT = ∞ on an acyclic input with an allowed common no-cycle output; reason: totalizes the case the source leaves undefined, as in the base mission
-- source:
--   Yi-Jun Chang, Yanyu Chen, Dipan Dey, Yonggang Jiang, Gopinath Mishra, Hung Thuan Nguyen, Mingyang Yang, The Complexity of Distributed Minimum Weight Cycle Approximation, STOC 2027 submission #440 (October 2026), citation basis published; papers/stoc2027-440/source.pdf (SHA-256 cdee21a6e698b7d3caf34f1990ab2132af424195b394467946a89faadca70ac1), Theorem 2, printed p. 4 / PDF p. 6; proof printed pp. 51–52 / PDF pp. 53–54; Conjecture 1.2, printed p. 3 / PDF p. 5.

import Definitions.Def_DistributedMWC440_UpperBound_Supplement_CongestLB

open scoped ENNReal
open MeasureTheory
noncomputable section

namespace DistributedMWC440.UpperBound.Supplement

/-- Theorem 2 (Lower bound), Chang et al., STOC 2027 submission #440, printed p. 4 / PDF p. 6
(proof printed pp. 51–52 / PDF pp. 53–54). Assume the Erdős girth conjecture for the integer
`k ≥ 1`. For every exponent `c > 0` (the `O(1)` in `ε ∈ n^(-O(1))`), message exponent `B` and ID
exponent `b ≥ 1` there are constants `C > 0`, `p` (and, for weighted inputs, a weight exponent
`q`) such that for every `ε(n) ≥ n^(-c)`, every algorithm `A` (any `n`-dependent state machine; it
contains every base-mission CONGEST protocol via `ofProtocol`) and every round budget `T` with
which `A` solves `(k+1-ε)`-Apx-MWC with high probability, `T(n) ≥ C n^((k+1)/(2k+1)) / (log n)^p`
for all large `n`. First clause: directed unweighted graphs; second: undirected weighted graphs. -/
theorem theorem_2 (k : ℕ) (hk : 1 ≤ k) (hE : ErdosGirth k) :
    (∀ c : ℝ, 0 < c → ∀ B b : ℕ, 1 ≤ b →
      ∃ C : ℝ, 0 < C ∧ ∃ p : ℕ, ∀ ε : ℕ → ℝ, (∀ n : ℕ, (n : ℝ) ^ (-c) ≤ ε n) →
        ∀ (A : LocalAlg) (T : ℕ → ℕ),
          SolvesDirected A (fun n => (k : ℝ) + 1 - ε n) b B T →
          ∃ n₀ : ℕ, ∀ n ≥ n₀,
            C * (n : ℝ) ^ (((k : ℝ) + 1) / (2 * k + 1)) / (Real.log n) ^ p ≤ (T n : ℝ)) ∧
    (∀ c : ℝ, 0 < c → ∀ B b : ℕ, 1 ≤ b →
      ∃ q : ℕ, ∃ C : ℝ, 0 < C ∧ ∃ p : ℕ, ∀ ε : ℕ → ℝ, (∀ n : ℕ, (n : ℝ) ^ (-c) ≤ ε n) →
        ∀ (A : LocalAlg) (T : ℕ → ℕ),
          SolvesWeighted A (fun n => (k : ℝ) + 1 - ε n) q b B T →
          ∃ n₀ : ℕ, ∀ n ≥ n₀,
            C * (n : ℝ) ^ (((k : ℝ) + 1) / (2 * k + 1)) / (Real.log n) ^ p ≤ (T n : ℝ)) := by sorry

end DistributedMWC440.UpperBound.Supplement
