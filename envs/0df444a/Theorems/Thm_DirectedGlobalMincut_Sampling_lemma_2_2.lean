-- Prove2me | Theorems.Thm_DirectedGlobalMincut_Sampling_lemma_2_2
-- name    : DirectedGlobalMincut.Sampling.lemma_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:04:29.132337+00:00
-- url     : https://prove2.me/theorems/cc002ee8-daae-4a81-8307-0489e040927d
-- title:
--   Lemma 2.2 — Conditional marginal contraction
-- statement:
--   Given a spanning out-arborescence $T$ rooted at $r$ and a nonnegative real vector $q$ dominating a point of $A_r$, one uniform randomized transition samples another spanning out-arborescence $T'$ with
--
--   $$\mathbb E[1_{T'}\mid T]\le\frac{1_T+q}{2}$$
--
--   coordinatewise. It uses at most one maximum-flow computation on a near-linear-size graph and near-linear additional work. The conditional statement is a kernel guarantee for every fixed input tree; each transition uses fresh randomness. No dominated point is part of the algorithm's input.
--
--   Differences from the source:
--   - encoding: finite vertex and arc sets → enumerated Fin n and Fin m over the published arc-identity digraph, with every listed arc active; reason: enumeration preserves all finite graphs, parallel arcs and loops; it introduces no simplicity or connectivity promise
--   - encoding: randomized sampling for arbitrary nonnegative real q → a finite exact-arithmetic RAM program with real Bernoulli sampling and a normalized PMF for its execution; reason: real q is not narrowed to rational data; binding transition laws supplies fresh randomness and summability is required for every asserted mean
--   - reading: soft-O(m) work and maximum-flow instance size → one uniform program and constants K,k before the graph, with bound ceil(K*(m+1)*log(2+n)^k); reason: this states the unspecified polylogarithmic exponent without letting constants depend on the instance; the additive 1 covers the finite empty-edge case in the generalization
--   - encoding: conditional expectation given T → the same program and fresh-randomness transition law satisfy the marginal inequality for every fixed T; reason: this is the conditional kernel needed when successive input trees are random
--   - generalization: G subject to the global input restrictions of section 1 → the structural assertion on any finite arc-identity digraph with a spanning out-arborescence; reason: the displayed assertions and their source proofs do not use weights, polynomial bounds or m>=n; all original instances are included
-- source:
--   Henry Fleischmann, Jason Li, Thatchaphol Saranurak, Benyu Wang, STOC 2027 submission #504 (October 2026), Lemma 2.2, p. 2 (PDF p. 2); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/504.pdf

import Mathlib
import Definitions.Def_DirectedGlobalMincut_Sampling_RealRAM

namespace DirectedGlobalMincut.Sampling

/-- Lemma 2.2 (p.2): the same fresh-randomness kernel applies to every fixed input tree T. -/
theorem lemma_2_2 :
    ∃ (P : RealProgram) (K : ℝ) (k : ℕ), 0 < K ∧
    ∀ n m (G : Graph n m) (r : Fin n) (T : Finset (Fin m)) (q : Fin m → ℝ),
      AllArcs G → IsTree G r T → Dominates G r q →
      let I := encGraphR G ++ [(r.val : ℝ)] ++
        List.ofFn (fun e => incidence T e) ++ List.ofFn q
      let B := softBudget K k n m
      ∀ O, IsMFOracleR O →
        let μ := realLaw P O I B
        RealRuns P O I B 1 B ∧
        (∀ s ∈ μ.support, MaskOutput m s ∧ IsTree G r (outputSet m s)) ∧
        ∀ e : Fin m, HasMean μ (fun s => incidence (outputSet m s) e) ∧
          Mean μ (fun s => incidence (outputSet m s) e) ≤ (incidence T e + q e) / 2 := by sorry

end DirectedGlobalMincut.Sampling
