-- Prove2me | Theorems.Thm_EdgeSublinearMWIS_Main_lemma_11
-- name    : EdgeSublinearMWIS.Main.lemma_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T13:42:17.026255+00:00
-- url     : https://prove2.me/theorems/fec9c087-4789-4a02-9d27-30fdcc12055e
-- title:
--   Lemma 11 — exclusion of the path-distribution outcome
-- statement:
--   Fix a hereditary class $\mathcal C$, an integer $a\ge2$, and a uniform bound $\operatorname{tw}(G)\le K|E(G)|^{1-1/a}$ for its members. One constant $B>0$ works for every real $\ell\ge1$: an integer $1\le p\le B\ell^{4a-2}$ is chosen before the graph and the costs. For every $G\in\mathcal C$ and real $x\in[0,1]^{V(G)}$, writing $k=x(V(G))$,
--   $$k\ge p,\quad e_G(x)\le k^2/p\quad\Longrightarrow\quad\text{the entire second alternative of Lemma 8 is impossible}.$$
--   The forbidden event includes the induced-subgraph size, the full endpoint law and every vertex marginal bound. Costs and the law are real, with no rationality restriction. This is the obstruction used to make the separator algorithm unconditional on the promised class.
--
--   Differences from the source:
--   - encoding: arbitrary finite simple graphs → graphs labeled by Fin n and finite vertex masks; reason: every finite graph admits such a labeling; induced injections transport class membership
--   - reading: for every ell at least one without an integer qualifier in the displayed result → every real ell at least one; reason: this includes all integer algorithmic instances and follows the displayed quantifier; the proof uses only real inequalities
--   - encoding: a fixed strongly edge-sublinear class, a satisfying (2), and O_C notation → heredity and a fixed uniform treewidth bound (2), with B before ell,G,x; reason: Theorem 5 makes the separator promise equivalent to a sublinear treewidth bound; retaining its fixed a,K loses no class instance and keeps constants uniform
-- source:
--   Édouard Bonnet, Yeonsu Chang, STOC 2027 submission #1044 (October 2026), Lemma 11, p.9 (PDF p.9), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1044.pdf

import Definitions.Def_EdgeSublinearMWIS_Main_Paths

namespace EdgeSublinearMWIS.Main

/-- Real ell ≥ 1 and real costs, as in the displayed quantifier of Lemma 11. -/
theorem lemma_11 (C : GraphClass) (a : ℕ) (K : ℝ)
    (hereditary : Hereditary C) (ha : 2 ≤ a) (bound : TreewidthBound C a K) :
    ∃ B : ℝ, 0 < B ∧ ∀ ell : ℝ, 1 ≤ ell →
      ∃ p : ℕ, 1 ≤ p ∧ (p : ℝ) ≤ B * ell ^ (4 * a - 2) ∧
        ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (x : Fin n → ℝ),
          C n G → (∀ v, 0 ≤ x v ∧ x v ≤ 1) →
          (p : ℝ) ≤ vertexSum x Finset.univ →
          edgeEnergy G x ≤ (vertexSum x Finset.univ) ^ 2 / p →
          ¬ ∃ (W : Finset (Fin n)) (f : List (List (Fin n) × ℝ)),
            PathOutcome G x ell W f := by sorry

end EdgeSublinearMWIS.Main
