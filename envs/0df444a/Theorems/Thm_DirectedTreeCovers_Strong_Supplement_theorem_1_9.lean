-- Prove2me | Theorems.Thm_DirectedTreeCovers_Strong_Supplement_theorem_1_9
-- name    : DirectedTreeCovers.Strong.Supplement.theorem_1_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:58:25.213189+00:00
-- url     : https://prove2.me/theorems/3ce4b784-6a44-4254-9b6a-cff61e3b2b95
-- title:
--   Theorem 1.9 — Prioritized strong cover
-- statement:
--   There is an absolute constant C>0 such that every finite directed graph G with n≥2 vertices, nonnegative real edge weights, every integer k≥4 and every priority ordering x₁,…,xₙ admit one finite randomized collection T of genuine tree-pairs. For an ordered pair u,v of finite roundtrip distance, let j be the smaller endpoint rank and put
--
--   $$q_j=\max\{1,\lceil k\log j/\log n\rceil\}.$$
--
--   Every outcome contains a pair Q with
--
--   $$d_Q(u,v)\le d_G(u,v)+(q_j-1)r_G(u,v).$$
--
--   The expected overlap at every vertex is at most Ck²n^(1/k). The guarantee uses the better endpoint in either position; in particular j≤floor(n^(1/k)) has zero additive error. One probability law serves every query.
--
--   This result gives a stronger guarantee to pairs involving high-priority vertices, while retaining the stated quadratic dependence on k in overlap.
--
--   Differences from the source:
--   - encoding: randomized finite sampling construction → a finite PMF of mass one and a list of tree-pairs at each atom; reason: the finite hierarchy and finite products in the source induce such a law; one outcome serves all queries and vertex overlap expectations
--   - encoding: absolute O bound → a positive real constant quantified before all instances and parameters; reason: this expresses the source bound with uniform constants and no asymptotic loss
--   - encoding: unreachable distance infinity and nonnegative real edge weights → published original-edge graph carrier and ENNReal distances; reason: preserves zero weights, absence of paths and actual edge identities; real roots use real division
--   - encoding: a priority list with ranks 1,...,n → a bijection to Fin n, adding one before taking the minimum endpoint rank; reason: zero-based storage changes no source rank or ceiling value; n≥2 makes log(n) positive
-- source:
--   Gur Lifshitz, Shiri Chechik, STOC 2027 submission #840 (October 2026), Theorem 1.9, printed p.5 (PDF p.6); papers/stoc2027-840/source.pdf, SHA-256 cfadd95d4c46b5ed7476d4f44a0fac01dbfa3050b82c7da814680249ce5b1947.

import Mathlib
import Definitions.Def_DirectedTreeCovers_Strong_Supplement_CoverLaws

namespace DirectedTreeCovers.Strong.Supplement

open EulerSparsify

/-- Theorem 1.9, printed p.5 / PDF p.6; §9.2, printed p.47 / PDF p.48.
The smaller endpoint rank controls stretch in either orientation. No extra
additive constant or multiplicative loss is present in the rank formula. -/
theorem theorem_1_9 :
    ∃ C : ℝ, 0 < C ∧ ∀ {V E : Type} [Fintype V] [Fintype E]
      (G : DiGraph V E), Nonnegative G → 2 ≤ Fintype.card V →
      ∀ k : ℕ, 4 ≤ k → ∀ ρ : Priority V, ∃ L : CoverLaw V E,
        (∀ ω, PrioritizedCover G k ρ (L.output ω)) ∧
        ∀ v : V, meanOverlap L v ≤
          C * (k : ℝ) ^ 2 * rootScale (Fintype.card V) k := by sorry

end DirectedTreeCovers.Strong.Supplement
