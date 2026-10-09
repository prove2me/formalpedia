-- Prove2me | Theorems.Thm_DistCov_Hilbert_errata_x_continuity
-- name    : DistCov.Hilbert.errata_x_continuity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:28:03.650464+00:00
-- url     : https://prove2.me/theorems/de2ca4cf-f3d2-4b75-b491-92c49d503e81
-- title:
--   Errata (x), pp. 28–29 (claim of p. 19) — β(µ)((v, w), s) = 0 for ρ-a.e. w, all v ∈ ℝᴷ and all s
-- statement:
--   Let $\mu_1,\mu_2$ be Borel probability measures on $\ell^2(\mathbb Z^+)$ with finite first moments and let
--   $$F(w,s)=\mu_1\{u\,;\,w(u)\le cs\}-\mu_2\{u\,;\,w(u)\le cs\}$$
--   be the barycenter $\beta(\mu)$ of $\mu=\mu_1-\mu_2$ under the Gaussian Crofton embedding. Fix $K\ge0$. If $F=0$ holds $(\rho\times\lambda)$-almost everywhere, then for $\rho$-a.e. $w\in\mathbb R^\infty$,
--   $$F\big((v,w),s\big)=0\qquad\text{for all } v\in\mathbb R^K \text{ and all } s\in\mathbb R,$$
--   where $(v,w)$ is the sequence with first $K$ coordinates $v$ and remaining coordinates those of $w$.
--
--   This is the claim at the end of the penultimate paragraph of the proof of Theorem 3.16, whose justification is supplied in Errata (x): it upgrades "for $\lambda^K$-a.e. $v$ and $\lambda$-a.e. $s$" to "for all $v$ and all $s$".
--
--   **Formalization Note.** Indices start at $0$, so $(v,w)$ takes coordinates $0,\dots,K-1$ from $v$ and coordinates $n\ge K$ from $w$. The paper pairs the tail of $u$ with $w$'s tail coordinates; under the IID law $\rho$ either pairing has the same distribution. The statement starts from the joint a.e. hypothesis on $\rho\times\lambda$, as the paper does; the passage to almost every $v$ and $s$ (Fubini, using the product structure of $\rho$) is part of what is to be proved. $K=0$ is allowed; the paper has $K\ge1$.
-- source:
--   Lyons, Distance covariance in metric spaces, arXiv:1106.5758 (version of 19 Dec. 2020), p. 19, proof of Theorem 3.16, first paragraph; Errata (x), pp. 28–29

import Mathlib
import Definitions.Def_DistCov_Hilbert_Setting

namespace DistCov.Hilbert

open MeasureTheory ProbabilityTheory

theorem errata_x_continuity (μ₁ μ₂ : Measure DistCov.Indep.L2N) [IsProbabilityMeasure μ₁]
    [IsProbabilityMeasure μ₂] (h₁ : DistCov.Indep.FiniteFirstMoment μ₁) (h₂ : DistCov.Indep.FiniteFirstMoment μ₂) (K : ℕ)
    (h : baryDiff μ₁ μ₂ =ᵐ[rho.prod volume] 0) :
    ∀ᵐ w ∂rho, ∀ (v : Fin K → ℝ) (s : ℝ), baryDiff μ₁ μ₂ (splice K v w, s) = 0 := by sorry

end DistCov.Hilbert
