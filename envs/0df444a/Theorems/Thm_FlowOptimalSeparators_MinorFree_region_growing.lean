-- Prove2me | Theorems.Thm_FlowOptimalSeparators_MinorFree_region_growing
-- name    : FlowOptimalSeparators.MinorFree.region_growing
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T00:09:04.652812+00:00
-- url     : https://prove2.me/theorems/5ede9084-facd-4d3a-ab3f-d3379535c1bc
-- title:
--   Lemma 8 — vertex-weighted region growing
-- statement:
--   Let $\delta\ge1$, let $G$ be a finite graph with integer vertex weights $1\le w(v)\le\delta$, and let $X$ be a nonempty vertex set. Distances use edge length $(w(u)+w(v))/2$. There is a deterministic program, given the distances from $X$, that returns $R$ with
--   $$X\subseteq R\subseteq B_G(X,2\delta),\qquad
--   |\partial R|\le\frac1\delta\ln\frac{w(V)}{w(X)}\,w(R).$$
--   It takes at most $C(m+n+\delta)$ scalar steps for one universal $C>0$. The boundary is internal, unreachable distances have explicit infinity flags, and the exact logarithmic coefficient and radius are retained.
--
--   Differences from the source:
--   - encoding: finite undirected simple graphs on arbitrary vertex sets → SimpleGraph (Fin n), with arbitrary duplicate-free adjacency-list orders; reason: vertex relabelling preserves all graph notions and CSR arrays have linear input size
--   - reading: an algorithm and its running time → one finite scalar arithmetic RAM program, unit-cost arithmetic and comparisons, indirect arrays, and charged independent uniform-index draws; reason: the paper does not specify a bit machine; the chunk brief fixes the arithmetic RAM reading, without graph or shortest-path oracles
--   - encoding: the distances from X are supplied → finite distances and explicit unreachable flags in the input arrays; reason: the distances are provided data in this lemma; no distance computation is charged as free preprocessing inside another algorithm
-- source:
--   Hung Le, Jack Spalding-Jamieson, STOC 2027 submission #1211 (October 2026), p. 23, Lemma 8, Eq. (32)

import Mathlib
import Definitions.Def_FlowOptimalSeparators_MinorFree_AlgorithmOutputs

set_option autoImplicit false

namespace FlowOptimalSeparators.MinorFree

/-- Lemma 8, p.23. The exact boundary coefficient and radius are retained. Distances
are supplied as input; the deterministic program is not given a candidate satisfying the bound. -/
theorem region_growing :
    ∃ (C : ℝ) (code : List Instruction), 0 < C ∧ DeterministicCode code ∧
      ∀ (n : ℕ) (G : Graph n) (A : AdjacencyInput G) (w : Fin n → ℕ)
        (δ : ℝ) (X : Finset (Fin n)),
        1 ≤ δ → (∀ v, 1 ≤ w v ∧ (w v : ℝ) ≤ δ) → X.Nonempty →
        let ns := growInputN A X w
        let rs := growInputR G X w δ
        (∀ ω, ∃ t, (ramRun ⟨code, []⟩ ns rs ω t).scalar.halted = true ∧
          (ramRun ⟨code, []⟩ ns rs ω t).fault = false ∧
          GrowOutput G X w δ (ramRun ⟨code, []⟩ ns rs ω t).scalar ∧
          (t : ℝ) ≤ C * ((edgeCount G : ℝ) + n + δ)) := by sorry

end FlowOptimalSeparators.MinorFree
