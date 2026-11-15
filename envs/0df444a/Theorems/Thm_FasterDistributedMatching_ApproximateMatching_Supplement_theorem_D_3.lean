-- Prove2me | Theorems.Thm_FasterDistributedMatching_ApproximateMatching_Supplement_theorem_D_3
-- name    : FasterDistributedMatching.ApproximateMatching.Supplement.theorem_D_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T03:36:51.909927+00:00
-- url     : https://prove2.me/theorems/8366da67-37e2-4f40-88d6-13e5bd009467
-- title:
--   Theorem D.3 — correctness of the independent-set recursion
-- statement:
--   Let $c$ be the constant of Lemma D.2. Logarithms are base two. There is $N_0$ such that the following holds for every $N\ge N_0$, every finite simple graph $\bar G$ with at most $N$ vertices, every integer $k$ with
--   $$(\log N)^{0.01}\le k\le(\log N)^{0.99},$$
--   and all routines $\mathrm{ALD.1}$, $\mathrm{ALD.2}$, $\mathrm{Half}$ meeting Lemma D.1, Lemma D.2 (with constant $c$) and the halving assumption of Lemma 4.4 for this $\bar G$, $N$, $k$:
--
--   1. Algorithm 1 terminates: the root call $\mathrm{AlmostMIS}(V(\bar G),N^2,N,h\equiv1)$ returns.
--   2. All subroutine calls are valid: every reached call of ALD.2, ALD.1 and Half meets the hypotheses of Lemma D.2, Lemma D.1 and the halving assumption respectively.
--   3. Every reached call $\mathrm{AlmostMIS}(U,M_U,B,h)$ terminates, and its output is an independent set $I\subseteq U$ with
--   $$|E(\bar G[U\setminus N_{\bar G}[I]])|<\frac{M_U}{B^2}.\qquad(6)$$
--   4. Consequently, ComputeMIS returns a maximal independent set of $\bar G$.
--
--   The threshold $N_0$ depends only on $c$, not on $\bar G$, $k$ or the routines. This is the correctness half of the paper's recursion interface (Lemma 4.4), which turns a halving routine into an MIS algorithm; the paper applies it to the line graph to obtain maximal matching (Corollary 1.3).
--
--   **Formalization Note** The routines are arbitrary functions meeting the input/output guarantees of Lemmas D.1, D.2 and the halving assumption, each only on inputs meeting its hypotheses; termination is a finite derivation of the big-step execution relation, and reached calls are generated from the root call.
--
--   Differences from the source:
--   - reading: "for sufficiently large N" with an absolute constant c of Lemma D.2 → for every real c there is N₀ such that every N ≥ N₀, graph, k in the range and conforming routines satisfy the conclusion; reason: the proof chooses N large after c and uniformly over Ḡ, k and the routines ("the following argument applies to every k in the stated range"); taking c to be the constant of Lemma D.2 gives the source's statement
--   - generalization: ALD.1, ALD.2 and Half are the specific deterministic LOCAL algorithms of [GG24] and Lemma 4.4, with round bounds and locally marked outputs → arbitrary functions of their arguments meeting the input/output guarantees of Lemma D.1, Lemma D.2 and the halving assumption; reason: Theorem D.3 makes no round claim and its proof uses only these guarantees ("only the partition and head-start refinement results of [GG24] are used as black boxes"); the actual algorithms are such functions, so the source's statement is a special case
--   - encoding: a fixed graph Ḡ with at most N vertices → a SimpleGraph on a finite type V : Type with Fintype.card V ≤ N; reason: every finite simple graph is isomorphic to one of these
--   - encoding: "terminates", "every reached call" and "all subroutine calls are valid" → a finite derivation of the inductive big-step relation Runs, the inductive predicate Reached generated from the root call of ComputeMIS, and AllCallsValid; reason: these are the operational meanings of the source's words for the deterministic recursion of Algorithm 1
--   - encoding: log, N^{1/k}, ε_B, B^{1/2+ε_B}, M_U → base-two logTwo, real powers, 1/(logTwo (logTwo B))², reals; reason: the source's conventions; Lean's 1/0 = 0 can only arise when log₂log₂B = 0, which no internal call in the stated range has
-- source:
--   Mohsen Ghaffari, Christoph Grunau, STOC 2027 submission #1024 (October 2026), Theorem D.3, printed p.27, PDF p.29 (proof printed pp.27–29, PDF pp.29–31); Algorithm 1 and Lemmas D.1–D.2, printed pp.25–26, PDF pp.27–28; Lemma 4.4, printed p.19, PDF p.21

import Mathlib
import Definitions.Def_FasterDistributedMatching_ApproximateMatching_Basic
import Definitions.Def_SmoothedMIS_IsMIS
import Definitions.Def_FasterDistributedMatching_ApproximateMatching_Supplement_Recursion

namespace FasterDistributedMatching.ApproximateMatching.Supplement

open Classical

/-- **Theorem D.3** (Correctness of the recursion; Ghaffari--Grunau, STOC 2027 submission #1024,
printed p. 27, PDF p. 29). For every constant `c` of Lemma D.2 there is `N₀` such that for every
`N ≥ N₀`, every finite simple graph `Ḡ` on at most `N` vertices, every integer
`k ∈ [(log N)^{0.01}, (log N)^{0.99}]`, and all routines `ALD.1`, `ALD.2`, `Half` meeting
Lemma D.1, Lemma D.2 (with `c`) and the halving assumption: Algorithm 1 terminates, all subroutine
calls are valid, every reached call `AlmostMIS(U, M_U, B, h)` returns an independent `I ⊆ U` with
`|E(Ḡ[U \ N_Ḡ[I]])| < M_U / B²`, and `ComputeMIS` returns an MIS of `Ḡ`. -/
theorem theorem_D_3 (c : ℝ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ (V : Type) [Fintype V] (G : SimpleGraph V), Fintype.card V ≤ N →
    ∀ k : ℕ, logTwo (N : ℝ) ^ (0.01 : ℝ) ≤ (k : ℝ) → (k : ℝ) ≤ logTwo (N : ℝ) ^ (0.99 : ℝ) →
    ∀ (ald1 : (V → ℕ) → ℕ → Finset (Finset V))
      (ald2 : Finset V → ℝ → ℝ → ℕ → (V → ℕ) → (V → ℕ))
      (half : Finset V → Finset (Finset V) → ℕ → Finset V),
    D1Spec G ald1 → D2Spec c G N ald2 → HalfSpec G N k half →
    let S : Setup V := ⟨G, N, k, ald1, ald2, half⟩
    -- Algorithm 1 terminates: the root call `AlmostMIS(V(Ḡ), N², N, h ≡ 1)` returns.
    (∃ I, S.Runs Finset.univ ((N : ℝ) ^ 2) (N : ℝ) (fun _ => 1) I) ∧
    -- All subroutine calls are valid.
    S.AllCallsValid c ∧
    -- Every reached call terminates and returns an independent `I ⊆ U` satisfying (6).
    (∀ (U : Finset V) (M B : ℝ) (h : V → ℕ), S.Reached U M B h →
      (∃ I, S.Runs U M B h I) ∧
      ∀ I, S.Runs U M B h I →
        I ⊆ U ∧ G.IsIndepSet (I : Set V) ∧
        (edgeCount G (removeNbhd G U I) : ℝ) < M / B ^ 2) ∧
    -- Consequently, `ComputeMIS` returns an MIS of `Ḡ`.
    (∀ I, S.Runs Finset.univ ((N : ℝ) ^ 2) (N : ℝ) (fun _ => 1) I →
      SmoothedMIS.IsMIS G (S.computeMISOutput I : Set V)) := by sorry

end FasterDistributedMatching.ApproximateMatching.Supplement
