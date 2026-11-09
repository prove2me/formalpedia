-- Prove2me | Theorems.Thm_DirectedGlobalMincut_Sampling_lemma_3_1
-- name    : DirectedGlobalMincut.Sampling.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:03:46.449389+00:00
-- url     : https://prove2.me/theorems/05a2d618-829d-4c8a-bc7d-c0e678072a4a
-- title:
--   Lemma 3.1 — Support Mixing Flow
-- statement:
--   Given a spanning out-arborescence $T$ rooted at $r$ and a nonnegative real vector $q$ dominating some point of $A_r$, one uniform randomized program constructs an integral nonnegative arc vector $f$ such that
--
--   $$\mathbb E[f_e]\le q_e\quad(e\in E),\qquad
--   \sum_{e\in E}f_e=n-1,$$
--
--   $$ (1_T+f)(\delta^-(S))\ge2
--   \quad\text{for every nonempty }S\subseteq V\setminus\{r\}.$$
--
--   The last two properties hold on each output, not only in expectation. The program uses at most one maximum-flow computation on a near-linear-size graph and near-linear additional work. A dominated point and its convex decomposition are neither given nor computed. The term flow in this result denotes an arc vector; it imposes no original-graph conservation or pointwise upper bound $f\le q$.
--
--   Differences from the source:
--   - encoding: finite vertex and arc sets → enumerated Fin n and Fin m over the published arc-identity digraph, with every listed arc active; reason: enumeration preserves all finite graphs, parallel arcs and loops; it introduces no simplicity or connectivity promise
--   - encoding: randomized sampling for arbitrary nonnegative real q → a finite exact-arithmetic RAM program with real Bernoulli sampling and a normalized PMF for its execution; reason: real q is not narrowed to rational data; binding transition laws supplies fresh randomness and summability is required for every asserted mean
--   - reading: soft-O(m) work and maximum-flow instance size → one uniform program and constants K,k before the graph, with bound ceil(K*(m+1)*log(2+n)^k); reason: this states the unspecified polylogarithmic exponent without letting constants depend on the instance; the additive 1 covers the finite empty-edge case in the generalization
--   - generalization: G subject to the global input restrictions of section 1 → the structural assertion on any finite arc-identity digraph with a spanning out-arborescence; reason: the displayed assertions and their source proofs do not use weights, polynomial bounds or m>=n; all original instances are included
-- source:
--   Henry Fleischmann, Jason Li, Thatchaphol Saranurak, Benyu Wang, STOC 2027 submission #504 (October 2026), Lemma 3.1, p. 3 (PDF p. 3); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/504.pdf

import Mathlib
import Definitions.Def_DirectedGlobalMincut_Sampling_RealRAM

namespace DirectedGlobalMincut.Sampling

/-- Lemma 3.1, first occurrence p.3. The dominated witness is not an algorithm input. -/
theorem lemma_3_1 :
    ∃ (P : RealProgram) (K : ℝ) (k : ℕ), 0 < K ∧
    ∀ n m (G : Graph n m) (r : Fin n) (T : Finset (Fin m)) (q : Fin m → ℝ),
      AllArcs G → IsTree G r T → Dominates G r q →
      let I := encGraphR G ++ [(r.val : ℝ)] ++
        List.ofFn (fun e => incidence T e) ++ List.ofFn q
      let B := softBudget K k n m
      ∀ O, IsMFOracleR O →
        let μ := realLaw P O I B
        RealRuns P O I B 1 B ∧
        (∀ s ∈ μ.support, (realOutput s).length = m ∧
          (∀ e : Fin m, ∃ z : ℕ, s.reg (e.val + 1) = z) ∧
          (∑ e : Fin m, s.reg (e.val + 1)) = (n : ℝ) - 1 ∧
          ∀ S, IsRootedCut r S →
            2 ≤ cutWeight G (fun e => incidence T e + s.reg (e.val + 1)) S) ∧
        ∀ e : Fin m, HasMean μ (fun s => s.reg (e.val + 1)) ∧
          Mean μ (fun s => s.reg (e.val + 1)) ≤ q e := by sorry

end DirectedGlobalMincut.Sampling
