-- Prove2me | Theorems.Thm_DistCov_Hilbert_Ddiff_eq_baryDiff
-- name    : DistCov.Hilbert.Ddiff_eq_baryDiff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:28:02.184305+00:00
-- url     : https://prove2.me/theorems/8ef9cead-b563-40bc-b40e-6b2736578f04
-- title:
--   (3.4), p. 11, and p. 18 — D(µ₁ − µ₂) = −2‖β_ϕ(µ₁ − µ₂)‖², with β_ϕ(µ)(w, s) = µ{u ; w(u) ≤ cs}
-- statement:
--   Let $\mu_1,\mu_2$ be Borel probability measures on $\ell^2(\mathbb Z^+)$ with finite first moments, let $\rho$, $\lambda$, $c$ and $w(u)$ be as in the Gaussian Crofton embedding, and let
--   $$F(w,s):=\mu_1\{u\,;\,w(u)\le cs\}-\mu_2\{u\,;\,w(u)\le cs\}\qquad (w\in\mathbb R^\infty,\ s\in\mathbb R),$$
--   which is the barycenter $\beta_\phi(\mu_1-\mu_2)$ of the signed measure $\mu_1-\mu_2$ under the embedding $\phi$. Then $F^2$ is integrable with respect to $\rho\times\lambda$ and
--   $$D(\mu_1-\mu_2) = -2\int F^2\,d(\rho\times\lambda) .$$
--
--   This is identity (3.4), $D(\mu)=-2\|\beta(\mu)\|^2$ for $\mu(\mathscr X)=0$, applied to the Gaussian embedding of $\ell^2(\mathbb Z^+)$. It reduces strong negative type of $\ell^2$ to showing that $F=0$ almost everywhere forces $\mu_1=\mu_2$.
--
--   **Formalization Note.** $D(\mu_1-\mu_2)$ is the energy expansion of the Setting file, and $\|\beta_\phi(\mu_1-\mu_2)\|^2_{L^2(\rho\times\lambda)}$ is written as the integral of $F^2$. Finite first moment means $\int\|u-o\|\,d\mu_i(u)<\infty$ for some $o$. Indices start at $0$.
-- source:
--   Lyons, Distance covariance in metric spaces, arXiv:1106.5758 (version of 19 Dec. 2020), p. 11, (3.4); p. 18, proof of Theorem 3.16, display β_ϕ(µ) : (w, s) ↦ µ{u ; w(u) ≤ cs}

import Mathlib
import Definitions.Def_DistCov_Hilbert_Setting

namespace DistCov.Hilbert

open MeasureTheory ProbabilityTheory

theorem Ddiff_eq_baryDiff (μ₁ μ₂ : Measure DistCov.Indep.L2N) [IsProbabilityMeasure μ₁]
    [IsProbabilityMeasure μ₂] (h₁ : DistCov.Indep.FiniteFirstMoment μ₁) (h₂ : DistCov.Indep.FiniteFirstMoment μ₂) :
    Integrable (fun p => baryDiff μ₁ μ₂ p ^ 2) (rho.prod volume) ∧
    DistCov.Indep.Ddiff μ₁ μ₂ = -2 * ∫ p, baryDiff μ₁ μ₂ p ^ 2 ∂(rho.prod volume) := by sorry

end DistCov.Hilbert
