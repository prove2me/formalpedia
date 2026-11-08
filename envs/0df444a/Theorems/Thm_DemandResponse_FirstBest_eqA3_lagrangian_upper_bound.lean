-- Prove2me | Theorems.Thm_DemandResponse_FirstBest_eqA3_lagrangian_upper_bound
-- name    : DemandResponse.FirstBest.eqA3_lagrangian_upper_bound
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-11-07T07:37:26.614194+00:00
-- url     : https://prove2.me/theorems/7136e4a9-10ad-47bd-bbce-6bd131a74162
-- title:
--   (A.3)–(A.5) weak duality — $J_P(\xi,\mathbb P^\nu)\le R_0(w/R_0)^{1+p/r}$ when $\bar V^\nu\le w<0$
-- statement:
--   In the demand-response model of Aïd, Possamaï and Touzi, fix an admissible pair $(\nu,\mathbb P)$ and a contract $\xi\in\mathcal C$ satisfying the participation constraint $J_A(\xi,\mathbb P^\nu)\ge R_0$. Write $\rho=\frac{rp}{r+p}$, $(f-g)(x)=\delta x$ with $\delta=\kappa-\theta$, and
--   $$\bar V^\nu:=\mathbb E^{\mathbb P}\Big[-e^{-\rho\left(\int_0^T(\delta X_t-c(\nu_t))dt-\frac h2\langle X\rangle_T\right)}\Big]\in[-\infty,0].$$
--   If $w<0$ is a real number with $\bar V^\nu\le w$, then
--   $$J_P(\xi,\mathbb P^\nu)\le R_0\Big(\frac{w}{R_0}\Big)^{1+\frac pr}.$$
--
--   This is the weak-duality half of the Lagrangian reduction (A.3)–(A.5): for a multiplier $\ell\ge0$ one has $J_P\le J_P+\ell(J_A-R_0)$, the integrand $U(-\xi-G^\nu_T)+\ell\,U_A(\xi+K^\nu_T)$ is maximised pointwise in $\xi$ by (A.4), which turns it into a multiple of $-e^{-\rho(K^\nu_T-G^\nu_T)}$, and the optimal multiplier $\ell^\star$ of (A.5) gives the bound. Here $K^\nu_T=\int_0^T(\kappa X_s-c(\nu_s))ds$ and $G^\nu_T=\int_0^T\theta X_sds+\frac h2\langle X\rangle_T$.
--
--   **Formalization Note** $\langle X\rangle_T$ is its almost-sure value $\int_0^T|\sigma(\beta_t)|^2dt$ under the admissible pair, as in the definitions of $J_P$ and $\bar V$. The bound is stated for every real upper bound $w<0$ of $\bar V^\nu$ (in particular for $w=\bar V$), which is the form used to pass to the supremum over efforts; the right-hand side is increasing in $w$ on $(-\infty,0)$.
-- source:
--   arXiv:1810.09063v3 (Aïd, Possamaï, Touzi), Appendix A.2, proof of Proposition 3.1, equations (A.3)–(A.5), p. 26

import Mathlib
import Definitions.Def_DemandResponse_FirstBest_Model

open MeasureTheory

namespace DemandResponse.FirstBest

/-- (A.3)–(A.5), upper bound for a fixed effort: if `(ν, ℙ)` is admissible, `ξ ∈ 𝒞` satisfies the
participation constraint `J_A(ξ, ℙ^ν) ≥ R₀`, and the reduced criterion
`-E^ℙ[exp(-ρ(∫₀ᵀ (δ X_t - c(ν_t)) dt - (h/2)⟨X⟩_T))]` is at most the real `w < 0`, then
`J_P(ξ, ℙ^ν) ≤ R₀ (w / R₀)^{1 + p/r}`. -/
theorem eqA3_lagrangian_upper_bound {N d : ℕ} (P : Params N d) (ξ : Path P → ℝ)
    (ν : Control P) (Q : Measure (Path P)) (hξ : IsContract P ξ) (hQ : Admissible P ν Q)
    (hPC : (P.R₀ : EReal) ≤ JA P ξ ν Q) (w : ℝ) (hw : w < 0)
    (hCw : -(((∫⁻ ω, ENNReal.ofReal (Real.exp (-rho P *
      ((∫ s in (0 : ℝ)..P.T, (delta P * Xr P s ω - cost P (ν.αr s ω) (ν.βr s ω))) -
        P.h / 2 * qvInt P ν P.T ω))) ∂Q) : ENNReal) : EReal) ≤ (w : EReal)) :
    JP P ξ ν Q ≤ ((P.R₀ * (w / P.R₀) ^ (1 + P.p / P.r) : ℝ) : EReal) := by sorry

end DemandResponse.FirstBest
