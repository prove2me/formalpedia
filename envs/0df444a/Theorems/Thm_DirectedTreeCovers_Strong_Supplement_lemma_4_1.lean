-- Prove2me | Theorems.Thm_DirectedTreeCovers_Strong_Supplement_lemma_4_1
-- name    : DirectedTreeCovers.Strong.Supplement.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:54:55.875055+00:00
-- url     : https://prove2.me/theorems/41dae5a2-6ef2-4160-947e-0f5fa1490dcf
-- title:
--   Lemma 4.1 — Algorithm 2 gives one tree-pair for both directions
-- statement:
--   Let G be a finite directed graph with arbitrary nonnegative real edge weights, and let k≥1. For every outcome of the independent hierarchy, let T be the actual output of Algorithm 2, using the strict clusters and the radius update with no shrinking term. Every output pair consists of genuine shortest-root-path trees in its induced search region. For each ordered pair u,v there is one pair Q in T with
--
--   $$r_Q(u,v)\le 2k\,r_G(u,v).$$
--
--   For finite graph roundtrip distance, this same Q contains both endpoints. Infinite graph roundtrips retain the displayed extended-distance inequality, following the component convention in §2.
--
--   This is the simultaneous two-direction stretch guarantee used by Theorem 1.1. No stretch or monotonicity property of the run is a hypothesis.
--
--   Differences from the source:
--   - reading: tree-pair containing u and v in the strongly connected proof component → extended roundtrip inequality on all pairs, with membership in the same pair required for finite-roundtrip pairs; reason: §2 permits componentwise construction; two isolated vertices cannot share a valid common-root pair, so membership across different components cannot be the intended global requirement
--   - encoding: unreachable distance infinity and nonnegative real edge weights → published original-edge graph carrier and ENNReal distances; reason: preserves zero weights, absence of paths and actual edge identities; real roots use real division
--   - encoding: unspecified deletion and shortest-path tie choices; searches in possibly empty strict clusters → fixed finite-set selectors and minimum-hop shortest-path ties; absent-root search slots are omitted; reason: fixes allowable choices once for the whole construction; minimum-hop ties prevent zero-weight parent cycles, and an empty cluster contributes no vertex or route and zero overlap
-- source:
--   Gur Lifshitz, Shiri Chechik, STOC 2027 submission #840 (October 2026), Lemma 4.1, printed p.14 (PDF p.15); papers/stoc2027-840/source.pdf, SHA-256 cfadd95d4c46b5ed7476d4f44a0fac01dbfa3050b82c7da814680249ce5b1947.

import Mathlib
import Definitions.Def_DirectedTreeCovers_Strong_Supplement_Roundtrip

namespace DirectedTreeCovers.Strong.Supplement

open EulerSparsify

/-- Lemma 4.1, printed p.14 / PDF p.15: the actual Algorithm 2 output,
with one pair for both directions, including zero weights and k=1. -/
theorem lemma_4_1 {V E : Type} [Fintype V] [Fintype E]
    (G : DiGraph V E) (hG : Nonnegative G) (k : ℕ) (hk : 1 ≤ k)
    (ω : Coins V k) :
    RoundtripCover G (2 * k) (roundtripConstruction G k ω).pairs := by sorry

end DirectedTreeCovers.Strong.Supplement
