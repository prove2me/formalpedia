-- Prove2me | Theorems.Thm_ClusterDecomp_lemma_3_4
-- name    : ClusterDecomp.lemma_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:09:42.9211+00:00
-- url     : https://prove2.me/theorems/8c61fcc6-3e2b-414d-928f-03e8202c9460
-- title:
--   Lemma 3.4, p.11 — the relative expansion satisfies $\varphi(U,B)\ge\varepsilon/4$
-- statement:
--   Under the hypotheses of Theorem 1.1, let $B$ be returned by Algorithm 1 on some $A_i$. For every $U\subseteq B$ with $0<\mathrm{vol}(U)<\mathrm{vol}(B)$ and $T=B\setminus U$,
--   $$\varphi(U,B)\ge\frac\varepsilon4,\qquad\text{equivalently}\qquad w(U,T)\ge\frac\varepsilon4\,\frac{\mathrm{vol}(T)}{\mathrm{vol}(B)}\,w(U,V\setminus B).$$
--
--   So the boundary between the two sides of any bipartition of $B$ is large compared with the boundary leaving $B$.
--
--   Differences from the source:
--   - generalization: integer weights with polynomial ratio (standing assumption, p.1) → any symmetric nonnegative real weights with positive degrees; reason: the argument uses neither integrality nor the ratio, and integer weights are an instance
--   - encoding: "the backbone returned by Algorithm 1", which computes an α-fair cut → every B = T ∖ {t} of every α-fair s,t-cut of H_A (Alg1Run); reason: the paper fixes nothing about the cut beyond fairness; the relation covers whatever the black box returns
--   - encoding: φ(U, B) with the convention +∞ when w(U, V ∖ B) = 0 → a value in ℝ≥0∞, with both displays stated as conjuncts; reason: the printed convention; the real-valued second display is its equivalent form
-- source:
--   Sun, Zhang, Zhou, Faster Cluster Decomposition with Stronger Bi-Criteria Guarantee, STOC 2027 submission (manuscript sha256 ba091f54…), Lemma 3.4 and the relative expansion, p.11 (PDF p.13)

import Mathlib
import Definitions.Def_ClusterDecomp_Alg1Run

open Finset
open scoped ENNReal

namespace ClusterDecomp

/-- **Lemma 3.4.**

Sun, Zhang, Zhou, *Faster Cluster Decomposition with Stronger Bi-Criteria Guarantee*, STOC 2027 submission
(manuscript sha256 ba091f54…), Lemma 3.4 and the relative expansion, p.11 (PDF p.13).

"Let B be the backbone returned by Algorithm 1. Then, for every U ⊆ B satisfying 0 < vol(U) < vol(B) and T = B ∖ U, we have
φ(U, B) ≥ ε/4. Equivalently, w(U, T) ≥ (ε/4)(vol(T)/vol(B)) w(U, V ∖ B)."

Both displays are stated, with `φ` valued in `ℝ≥0∞` and the printed convention `+∞` when `w(U, V ∖ B) = 0`. -/
theorem lemma_3_4 {V : Type*} [Fintype V] [DecidableEq V] (G : WGraph V) {k : ℕ} {A : Fin k → Finset V}
    {ε p : ℝ} (hF : Family G k A ε p) (i : Fin k) {B : Finset V} (hB : Alg1Run G (A i) ε p B)
    {U : Finset V} (hU : U ⊆ B) (hU0 : 0 < G.vol U) (hUB : G.vol U < G.vol B) :
    ENNReal.ofReal (ε / 4) ≤ G.relExp U B ∧
      ε / 4 * (G.vol (B \ U) / G.vol B) * G.cut U Bᶜ ≤ G.cut U (B \ U) := by sorry

end ClusterDecomp
