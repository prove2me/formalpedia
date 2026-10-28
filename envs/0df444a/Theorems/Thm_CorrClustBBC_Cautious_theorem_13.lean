-- Prove2me | Theorems.Thm_CorrClustBBC_Cautious_theorem_13
-- name    : CorrClustBBC.Cautious.theorem_13
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:27:06.555232+00:00
-- url     : https://prove2.me/theorems/8d5c1ac9-81d8-46d0-9182-d15231805fb8
-- title:
--   Theorem 13, p. 100 — every run of Algorithm Cautious makes at most (9/δ² + 5)·m_OPT mistakes, δ = 1/44
-- statement:
--   Let $G$ be a complete graph on a finite vertex set $V$ whose edges are labelled $+$ or $-$, and let $\delta=1/44$. Algorithm Cautious has at least one run on $G$, and every run — for every choice of pivot vertices and every order of removals in step 1(b) — outputs a clustering $\mathcal A$ such that, for every clustering $D$ of $V$,
--   $$m_{\mathcal A}\ \le\ \Big(\frac{9}{\delta^2}+5\Big)\,m_D .$$
--   Equivalently, $m_{\mathrm{Cautious}}\le (9/\delta^2+5)\,m_{\mathrm{OPT}}$; numerically the factor is $17\,429$.
--
--   This is the first constant-factor approximation for minimizing disagreements in correlation clustering on complete graphs.
--
--   **Formalization Note** "$m_{\mathrm{OPT}}$" is the least number of mistakes of any clustering, so a bound against every clustering $D$ is the same statement. The first part of the statement, that a run exists, rules out a vacuous reading in which the bound holds because the algorithm never produces an output.
--
--   Differences from the source:
--   - encoding: m_OPT → m_D for every clustering D; reason: m_OPT is the minimum over all clusterings, so the two statements are equivalent.
--   - reading: m_Cautious, the cost of the output of Cautious → Cautious has a run on G, and the output of every run (every pivot choice, every removal order) satisfies the bound; reason: the algorithm picks an arbitrary vertex and removes an arbitrary bad vertex, so its cost is that of every run, and that it produces an output at all is implicit in calling it an algorithm.
--   - reading: "repeat until no vertices are left or until all the produced sets A(v) are empty" → the run may stop exactly when every remaining vertex, tried as the pivot, has some execution of steps 1(a)–(c) producing ∅; reason: the phrase is ambiguous; this is the reading under which "all the produced sets are empty" refers to every remaining vertex.
--   - reading: N⁺(v), δ-goodness and the "y ∈ V" of step 1(c) in every iteration after the first → taken in the graph induced on the vertices not yet clustered (the current set R of the run); reason: step 2 deletes A(v) "from the set of vertices" before repeating, and the proof of Theorem 7 (p. 99) argues in "the remaining graph G \ (⋃_{ℓ<i} A_ℓ)".
-- source:
--   Bansal, Blum, Chawla, Correlation Clustering, Machine Learning 56 (2004) 89–113, p. 100, Theorem 13 (Algorithm Cautious p. 97)

import Mathlib
import Definitions.Def_CorrClustBBC_Cautious_Setting

namespace CorrClustBBC.Cautious
theorem theorem_13 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∃ (L : List (Finset V × Finset V × Finset V)) (Z : Finset V), Run G Finset.univ L Z) ∧
      ∀ (L : List (Finset V × Finset V × Finset V)) (Z : Finset V), Run G Finset.univ L Z →
        ∀ D : Setoid V,
          (mistakes G (sameCluster L) : ℝ) ≤ (9 / δ44 ^ 2 + 5) * (mistakes G D.r : ℝ) := by sorry
end CorrClustBBC.Cautious
