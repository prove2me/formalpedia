-- Prove2me | Theorems.Thm_DirectedTreeCovers_Strong_Supplement_lemma_4_2
-- name    : DirectedTreeCovers.Strong.Supplement.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:55:28.447308+00:00
-- url     : https://prove2.me/theorems/3ec3984c-8bab-4679-98c8-73d2a8095a32
-- title:
--   Lemma 4.2 — Expected level and total strict bunch sizes
-- statement:
--   Let B_i(v) be the roots of level i whose Algorithm 2 strict clusters contain v, and let B(v) be their union over all levels. There is an absolute constant C>0 such that for every finite nonnegatively weighted directed graph, k≥1, v∈V and 0≤i<k,
--
--   $$\mathbb E|B_i(v)|\le C n^{1/k},\qquad \mathbb E|B(v)|\le C k n^{1/k}.$$
--
--   Both expectations use the published independent, unforced hierarchy law with retention probability n^(−1/k). Radii, clusters and bunches are computed from that law’s outcomes. The total bound is a separate conclusion, not just a per-level assertion.
--
--   These estimates give the overlap control for the strict-cluster roundtrip cover.
--
--   Differences from the source:
--   - encoding: absolute O bound → a positive real constant quantified before all instances and parameters; reason: this expresses the source bound with uniform constants and no asymptotic loss
--   - encoding: unreachable distance infinity and nonnegative real edge weights → published original-edge graph carrier and ENNReal distances; reason: preserves zero weights, absence of paths and actual edge identities; real roots use real division
--   - encoding: unspecified deletion and shortest-path tie choices; searches in possibly empty strict clusters → fixed finite-set selectors and minimum-hop shortest-path ties; absent-root search slots are omitted; reason: fixes allowable choices once for the whole construction; minimum-hop ties prevent zero-weight parent cycles, and an empty cluster contributes no vertex or route and zero overlap
-- source:
--   Gur Lifshitz, Shiri Chechik, STOC 2027 submission #840 (October 2026), Lemma 4.2, printed p.15 (PDF p.16); papers/stoc2027-840/source.pdf, SHA-256 cfadd95d4c46b5ed7476d4f44a0fac01dbfa3050b82c7da814680249ce5b1947.

import Mathlib
import Definitions.Def_DirectedTreeCovers_Strong_Supplement_CoverLaws

namespace DirectedTreeCovers.Strong.Supplement

open EulerSparsify

/-- Lemma 4.2, printed p.15 / PDF p.16. BOTH levelwise and total bounds;
the absolute constant precedes all graph types, weights, vertices and parameters. -/
theorem lemma_4_2 :
    ∃ C : ℝ, 0 < C ∧ ∀ {V E : Type} [Fintype V] [Fintype E]
      (G : DiGraph V E), Nonnegative G → ∀ k : ℕ, 1 ≤ k → ∀ v : V,
      (∀ i : ℕ, i < k →
        hierarchyMean k (fun ω => (strictBunchAt G k ω i v).card) ≤
          C * rootScale (Fintype.card V) k) ∧
      hierarchyMean k (fun ω => (strictBunch G k ω v).card) ≤
        C * (k : ℝ) * rootScale (Fintype.card V) k := by sorry

end DirectedTreeCovers.Strong.Supplement
