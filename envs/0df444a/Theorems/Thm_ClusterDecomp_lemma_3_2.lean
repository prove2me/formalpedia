-- Prove2me | Theorems.Thm_ClusterDecomp_lemma_3_2
-- name    : ClusterDecomp.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:09:32.169199+00:00
-- url     : https://prove2.me/theorems/cdc2e711-472a-4d14-87d8-c3466586460b
-- title:
--   Lemma 3.2, p.10 — the backbone has positive volume and $\phi_G(B)\le(1+\varepsilon/16)p$
-- statement:
--   Let $A$ have positive volume with $\phi_G(A)\le p$, where $p,\varepsilon>0$, and let $B$ be the backbone returned by Algorithm 1 on $A$. Then
--   $$\mathrm{vol}(B)>0,\qquad \phi_G(B)\le\alpha p=\Bigl(1+\frac{\varepsilon}{16}\Bigr)p.$$
--
--   So trimming loses at most a factor $\alpha$ in outer conductance.
--
--   Differences from the source:
--   - generalization: integer weights with polynomial ratio (standing assumption, p.1) → any symmetric nonnegative real weights with positive degrees; reason: the argument uses neither integrality nor the ratio, and integer weights are an instance
--   - encoding: "the backbone returned by Algorithm 1", which computes an α-fair cut → every B = T ∖ {t} of every α-fair s,t-cut of H_A (Alg1Run); reason: the paper fixes nothing about the cut beyond fairness; the relation covers whatever the black box returns
--   - generalization: 0 < ε ≤ 1 (Theorem 1.1) → ε > 0; reason: ε ≤ 1 is not used; values up to 1 are instances
-- source:
--   Sun, Zhang, Zhou, Faster Cluster Decomposition with Stronger Bi-Criteria Guarantee, STOC 2027 submission (manuscript sha256 ba091f54…), Lemma 3.2, p.10 (PDF p.12)

import Mathlib
import Definitions.Def_ClusterDecomp_Alg1Run

open Finset
open scoped ENNReal

namespace ClusterDecomp

/-- **Lemma 3.2.**

Sun, Zhang, Zhou, *Faster Cluster Decomposition with Stronger Bi-Criteria Guarantee*, STOC 2027 submission
(manuscript sha256 ba091f54…), Lemma 3.2, p.10 (PDF p.12).

"Let B be the backbone returned by Algorithm 1. Then, vol(B) > 0 and ϕG(B) ≤ αp = (1 + ε/16) p."

The hypotheses are the requirement of Algorithm 1 (a positive-volume `A` with `ϕ_G(A) ≤ p`), with `p, ε > 0`. The claim holds
for every `α`-fair cut. The bound `ε ≤ 1` is not needed. -/
theorem lemma_3_2 {V : Type*} [Fintype V] [DecidableEq V] (G : WGraph V) (hG : G.PosDeg) (A : Finset V)
    (ε p : ℝ) (hε : 0 < ε) (hp : 0 < p) (hA : 0 < G.vol A) (hAp : G.phiOut A ≤ p) (B : Finset V)
    (hB : Alg1Run G A ε p B) :
    0 < G.vol B ∧ G.phiOut B ≤ (1 + ε / 16) * p := by sorry

end ClusterDecomp
