-- Prove2me | Theorems.Thm_ClusterDecomp_lemma_3_3
-- name    : ClusterDecomp.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:09:28.809549+00:00
-- url     : https://prove2.me/theorems/697571a8-6ab4-4316-97fc-cfa8ddd614be
-- title:
--   Lemma 3.3, p.10 — $w(U,V\setminus B)\le\alpha(w(U,B\setminus U)+\beta\,\mathrm{vol}(U))$
-- statement:
--   Let $B$ be the backbone returned by Algorithm 1, with $\alpha=1+\varepsilon/16$ and $\beta=(1+\varepsilon/10)p$. For every $U\subseteq B$,
--   $$w(U,V\setminus B)\le\alpha\bigl(w(U,B\setminus U)+\beta\,\mathrm{vol}(U)\bigr).$$
--
--   The bound holds for all $U$ simultaneously from the single flow that witnesses fairness, and it replaces the local search used in earlier work.
--
--   Differences from the source:
--   - generalization: integer weights with polynomial ratio (standing assumption, p.1) → any symmetric nonnegative real weights with positive degrees; reason: the argument uses neither integrality nor the ratio, and integer weights are an instance
--   - encoding: "the backbone returned by Algorithm 1", which computes an α-fair cut → every B = T ∖ {t} of every α-fair s,t-cut of H_A (Alg1Run); reason: the paper fixes nothing about the cut beyond fairness; the relation covers whatever the black box returns
--   - generalization: A with ϕ_G(A) ≤ p and 0 < ε ≤ 1 → any A, any ε > 0; reason: neither is used; the source case is an instance
-- source:
--   Sun, Zhang, Zhou, Faster Cluster Decomposition with Stronger Bi-Criteria Guarantee, STOC 2027 submission (manuscript sha256 ba091f54…), Lemma 3.3, p.10 (PDF p.12)

import Mathlib
import Definitions.Def_ClusterDecomp_Alg1Run

open Finset
open scoped ENNReal

namespace ClusterDecomp

/-- **Lemma 3.3.**

Sun, Zhang, Zhou, *Faster Cluster Decomposition with Stronger Bi-Criteria Guarantee*, STOC 2027 submission
(manuscript sha256 ba091f54…), Lemma 3.3, p.10 (PDF p.12).

"Let B be the backbone returned by Algorithm 1. Then, it holds for every U ⊆ B that
w(U, V ∖ B) ≤ α (w(U, B ∖ U) + β vol(U))."

Here `α = 1 + ε/16` and `β = (1 + ε/10)p`, and the claim holds for every `α`-fair cut. The bound `ε ≤ 1` and `ϕ_G(A) ≤ p` are not
needed. -/
theorem lemma_3_3 {V : Type*} [Fintype V] [DecidableEq V] (G : WGraph V) (hG : G.PosDeg) (A : Finset V)
    (ε p : ℝ) (hε : 0 < ε) (hp : 0 < p) (B : Finset V) (hB : Alg1Run G A ε p B)
    (U : Finset V) (hU : U ⊆ B) :
    G.cut U Bᶜ ≤ (1 + ε / 16) * (G.cut U (B \ U) + (1 + ε / 10) * p * G.vol U) := by sorry

end ClusterDecomp
