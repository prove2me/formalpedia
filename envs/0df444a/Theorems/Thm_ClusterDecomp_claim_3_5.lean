-- Prove2me | Theorems.Thm_ClusterDecomp_claim_3_5
-- name    : ClusterDecomp.claim_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:09:27.706274+00:00
-- url     : https://prove2.me/theorems/e58e7188-932b-42df-9f43-ddc70f67d962
-- title:
--   Claim 3.5, p.11 — $w(U,T)\ge\sigma\min\{\mathrm{vol}(U),\mathrm{vol}(T)\}$ and $\sigma\ge\frac25\varepsilon p$
-- statement:
--   Under the hypotheses of Theorem 1.1, let $B$ be returned by Algorithm 1 on some $A_i$, let $U\subseteq B$ with $0<\mathrm{vol}(U)<\mathrm{vol}(B)$, and let $T=B\setminus U$. With
--   $$\sigma=\frac{\rho_G(k+1)-\alpha\beta}{1+\alpha},$$
--   we have
--   $$w(U,T)\ge\sigma\min\{\mathrm{vol}(U),\mathrm{vol}(T)\},\qquad \sigma\ge\frac25\varepsilon p.$$
--
--   Here $\alpha=1+\varepsilon/16$ and $\beta=(1+\varepsilon/10)p$. This is where the gap between $\rho_G(k+1)$ and $p$ enters.
--
--   Differences from the source:
--   - generalization: integer weights with polynomial ratio (standing assumption, p.1) → any symmetric nonnegative real weights with positive degrees; reason: the argument uses neither integrality nor the ratio, and integer weights are an instance
--   - encoding: "the backbone returned by Algorithm 1", which computes an α-fair cut → every B = T ∖ {t} of every α-fair s,t-cut of H_A (Alg1Run); reason: the paper fixes nothing about the cut beyond fairness; the relation covers whatever the black box returns
--   - generalization: ρ_G(k+1) in the formula → any real r with r ≤ ρ_G(k+1) and (1+ε)p ≤ r; reason: U, T (resp. S) exist here, so ρ_G(k+1) < ⊤ and r = ρ_G(k+1) is the printed statement
-- source:
--   Sun, Zhang, Zhou, Faster Cluster Decomposition with Stronger Bi-Criteria Guarantee, STOC 2027 submission (manuscript sha256 ba091f54…), Claim 3.5 and the definition of σ, p.11 (PDF p.13)

import Mathlib
import Definitions.Def_ClusterDecomp_Alg1Run

open Finset
open scoped ENNReal

namespace ClusterDecomp

/-- **Claim 3.5.**

Sun, Zhang, Zhou, *Faster Cluster Decomposition with Stronger Bi-Criteria Guarantee*, STOC 2027 submission
(manuscript sha256 ba091f54…), Claim 3.5, p.11 (PDF p.13), with the hypotheses of Lemma 3.4.

"To prove Lemma 3.4, we set σ ≜ (ρG(k + 1) − αβ)/(1 + α), and first prove the following claim. Claim 3.5. For T = B ∖ U, we have
w(U, T) ≥ σ min{vol(U), vol(T)} and σ ≥ (2/5)εp."

**Formalization Note.** `σ` needs a real value of `ρ_G(k+1)`, and `r` is any real with `r ≤ ρ_G(k+1)` and `(1+ε)p ≤ r`. Since `U` and `T` exist
here, `ρ_G(k+1) < ⊤`, and `r = ρ_G(k+1)` is the printed statement. -/
theorem claim_3_5 {V : Type*} [Fintype V] [DecidableEq V] (G : WGraph V) {k : ℕ} {A : Fin k → Finset V}
    {ε p : ℝ} (hF : Family G k A ε p) (i : Fin k) {B : Finset V} (hB : Alg1Run G (A i) ε p B)
    {U : Finset V} (hU : U ⊆ B) (hU0 : 0 < G.vol U) (hUB : G.vol U < G.vol B)
    (r : ℝ) (hr : ENNReal.ofReal r ≤ G.rho (k + 1)) (hr' : (1 + ε) * p ≤ r)
    (σ : ℝ) (hσ : σ = (r - (1 + ε / 16) * ((1 + ε / 10) * p)) / (1 + (1 + ε / 16))) :
    σ * min (G.vol U) (G.vol (B \ U)) ≤ G.cut U (B \ U) ∧ 2 / 5 * ε * p ≤ σ := by sorry

end ClusterDecomp
