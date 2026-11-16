-- Prove2me | Theorems.Thm_DirectedTreeCovers_Strong_Supplement_theorem_1_8
-- name    : DirectedTreeCovers.Strong.Supplement.theorem_1_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:57:13.942197+00:00
-- url     : https://prove2.me/theorems/64b2ad5f-2523-41d3-b5d2-aca9c1c1bbdf
-- title:
--   Theorem 1.8 — Sourcewise strong cover
-- statement:
--   There is an absolute constant C>0 such that for every finite nonnegatively weighted directed graph G, every integer k≥1 and every nonempty S⊆V, one finite randomized tree-pair collection T satisfies, in each outcome,
--
--   $$\forall u\in S\ \forall v\in V:\ r_G(u,v)<\infty\ \Longrightarrow\ \exists Q\in\mathcal T:\ d_Q(u,v)\le d_G(u,v)+(k-1)r_G(u,v).$$
--
--   Every vertex v∈V belongs in expectation to at most Ck|S|^(1/k) pairs. This includes vertices outside S. All selected edges and weights belong to G, and paths may leave S. At k=1 the displayed guarantee is exact.
--
--   This is the source-restricted cover guarantee, with a single mass-one preprocessing law for all relevant queries and all overlap expectations.
--
--   Differences from the source:
--   - encoding: randomized finite sampling construction → a finite PMF of mass one and a list of tree-pairs at each atom; reason: the finite hierarchy and finite products in the source induce such a law; one outcome serves all queries and vertex overlap expectations
--   - encoding: absolute O bound → a positive real constant quantified before all instances and parameters; reason: this expresses the source bound with uniform constants and no asymptotic loss
--   - encoding: unreachable distance infinity and nonnegative real edge weights → published original-edge graph carrier and ENNReal distances; reason: preserves zero weights, absence of paths and actual edge identities; real roots use real division
-- source:
--   Gur Lifshitz, Shiri Chechik, STOC 2027 submission #840 (October 2026), Theorem 1.8, printed p.5 (PDF p.6); papers/stoc2027-840/source.pdf, SHA-256 cfadd95d4c46b5ed7476d4f44a0fac01dbfa3050b82c7da814680249ce5b1947.

import Mathlib
import Definitions.Def_DirectedTreeCovers_Strong_Supplement_CoverLaws

namespace DirectedTreeCovers.Strong.Supplement

open EulerSparsify

/-- Theorem 1.8, printed p.5 / PDF p.6; §9.1, printed p.44 / PDF p.45.
All k≥1 and nonempty source sets; overlap at EVERY vertex, including outside S. -/
theorem theorem_1_8 :
    ∃ C : ℝ, 0 < C ∧ ∀ {V E : Type} [Fintype V] [Fintype E]
      (G : DiGraph V E), Nonnegative G → ∀ k : ℕ, 1 ≤ k →
      ∀ S : Finset V, S.Nonempty → ∃ L : CoverLaw V E,
        (∀ ω, SourcewiseCover G k S (L.output ω)) ∧
        ∀ v : V, meanOverlap L v ≤ C * (k : ℝ) * rootScale S.card k := by sorry

end DirectedTreeCovers.Strong.Supplement
