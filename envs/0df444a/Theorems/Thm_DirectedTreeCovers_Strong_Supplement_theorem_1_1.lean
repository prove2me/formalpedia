-- Prove2me | Theorems.Thm_DirectedTreeCovers_Strong_Supplement_theorem_1_1
-- name    : DirectedTreeCovers.Strong.Supplement.theorem_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:56:22.875434+00:00
-- url     : https://prove2.me/theorems/fdd06f05-7d83-4e3d-95ee-cb484c39b36e
-- title:
--   Theorem 1.1 — Roundtrip cover with low expected overlap
-- statement:
--   There is an absolute constant C>0 such that every finite directed graph G with nonnegative real edge weights and every integer k≥1 admit one finite randomized collection T of genuine tree-pairs. Every outcome simultaneously satisfies
--
--   $$\forall u,v\in V\quad \exists Q\in\mathcal T:\quad r_Q(u,v)\le 2k\,r_G(u,v).$$
--
--   When r_G(u,v) is finite, the same pair contains both endpoints. At every vertex v, including vertices in singleton components, the expected number of pairs whose union support contains v is at most
--
--   $$C k n^{1/k}.$$
--
--   The preprocessing law has total mass one; it is chosen once for the entire collection, independently of the query. This result provides simultaneous roundtrip approximation within a single pair, rather than two independently selected directional pairs.
--
--   Differences from the source:
--   - encoding: randomized finite sampling construction → a finite PMF of mass one and a list of tree-pairs at each atom; reason: the finite hierarchy and finite products in the source induce such a law; one outcome serves all queries and vertex overlap expectations
--   - encoding: absolute O bound → a positive real constant quantified before all instances and parameters; reason: this expresses the source bound with uniform constants and no asymptotic loss
--   - reading: tree-pair containing u and v in the strongly connected proof component → extended roundtrip inequality on all pairs, with membership in the same pair required for finite-roundtrip pairs; reason: §2 permits componentwise construction; two isolated vertices cannot share a valid common-root pair, so membership across different components cannot be the intended global requirement
--   - encoding: unreachable distance infinity and nonnegative real edge weights → published original-edge graph carrier and ENNReal distances; reason: preserves zero weights, absence of paths and actual edge identities; real roots use real division
-- source:
--   Gur Lifshitz, Shiri Chechik, STOC 2027 submission #840 (October 2026), Theorem 1.1, printed p.3 (PDF p.4); papers/stoc2027-840/source.pdf, SHA-256 cfadd95d4c46b5ed7476d4f44a0fac01dbfa3050b82c7da814680249ce5b1947.

import Mathlib
import Definitions.Def_DirectedTreeCovers_Strong_Supplement_CoverLaws

namespace DirectedTreeCovers.Strong.Supplement

open EulerSparsify

/-- Theorem 1.1, printed p.3 / PDF p.4. A single mass-one preprocessing
law supplies one collection for all queries and every per-vertex expectation. -/
theorem theorem_1_1 :
    ∃ C : ℝ, 0 < C ∧ ∀ {V E : Type} [Fintype V] [Fintype E]
      (G : DiGraph V E), Nonnegative G → ∀ k : ℕ, 1 ≤ k →
      ∃ L : CoverLaw V E,
        (∀ ω, RoundtripCover G (2 * k) (L.output ω)) ∧
        ∀ v : V, meanOverlap L v ≤ C * (k : ℝ) * rootScale (Fintype.card V) k := by sorry

end DirectedTreeCovers.Strong.Supplement
