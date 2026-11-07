-- Prove2me | Theorems.Thm_ClusterDecomp_corollary_3_6
-- name    : ClusterDecomp.corollary_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:09:51.10142+00:00
-- url     : https://prove2.me/theorems/95376541-ddb1-414e-b135-73c8829a4216
-- title:
--   Corollary 3.6, p.13 — $w(U,T)/\mathrm{vol}(U)\ge\frac\varepsilon9\max\{\phi_G(U),\phi_G(T)\}$
-- statement:
--   Under the hypotheses of Theorem 1.1, let $B$ be returned by Algorithm 1 on some $A_i$. For every $U\subseteq B$ with $0<\mathrm{vol}(U)\le\mathrm{vol}(B)/2$ and $T=B\setminus U$,
--   $$\frac{w(U,T)}{\mathrm{vol}(U)}\ge\frac\varepsilon9\max\{\phi_G(U),\phi_G(T)\}.$$
--
--   Together with the definition of $\rho_G(k+1)$ this gives the inner conductance of the backbone.
--
--   Differences from the source:
--   - generalization: integer weights with polynomial ratio (standing assumption, p.1) → any symmetric nonnegative real weights with positive degrees; reason: the argument uses neither integrality nor the ratio, and integer weights are an instance
--   - encoding: "the backbone returned by Algorithm 1", which computes an α-fair cut → every B = T ∖ {t} of every α-fair s,t-cut of H_A (Alg1Run); reason: the paper fixes nothing about the cut beyond fairness; the relation covers whatever the black box returns
-- source:
--   Sun, Zhang, Zhou, Faster Cluster Decomposition with Stronger Bi-Criteria Guarantee, STOC 2027 submission (manuscript sha256 ba091f54…), Corollary 3.6, p.13 (PDF p.15)

import Mathlib
import Definitions.Def_ClusterDecomp_Alg1Run

open Finset
open scoped ENNReal

namespace ClusterDecomp

/-- **Corollary 3.6.**

Sun, Zhang, Zhou, *Faster Cluster Decomposition with Stronger Bi-Criteria Guarantee*, STOC 2027 submission
(manuscript sha256 ba091f54…), Corollary 3.6, p.13 (PDF p.15).

"Let B be the backbone returned by Algorithm 1. Then, for every U ⊆ B satisfying 0 < vol(U) ≤ vol(B)/2 and T = B ∖ U, we have
w(U, T)/vol(U) ≥ (ε/9) max{ϕG(U), ϕG(T)}."

`vol(T) ≥ vol(U) > 0` here, so both conductances are at positive volume. -/
theorem corollary_3_6 {V : Type*} [Fintype V] [DecidableEq V] (G : WGraph V) {k : ℕ} {A : Fin k → Finset V}
    {ε p : ℝ} (hF : Family G k A ε p) (i : Fin k) {B : Finset V} (hB : Alg1Run G (A i) ε p B)
    {U : Finset V} (hU : U ⊆ B) (hU0 : 0 < G.vol U) (hUB : G.vol U ≤ G.vol B / 2) :
    ε / 9 * max (G.phiOut U) (G.phiOut (B \ U)) ≤ G.cut U (B \ U) / G.vol U := by sorry

end ClusterDecomp
