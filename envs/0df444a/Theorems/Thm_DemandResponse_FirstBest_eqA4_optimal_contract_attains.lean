-- Prove2me | Theorems.Thm_DemandResponse_FirstBest_eqA4_optimal_contract_attains
-- name    : DemandResponse.FirstBest.eqA4_optimal_contract_attains
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-11-07T07:37:28.200821+00:00
-- url     : https://prove2.me/theorems/7e13f9fe-1cd1-40b1-b56c-5f7fafdb6696
-- title:
--   (A.4)–(A.5) attainment — the Lagrangian contract gives $J_P=R_0(\bar V^\nu/R_0)^{1+p/r}$
-- statement:
--   In the demand-response model of Aïd, Possamaï and Touzi, fix an admissible pair $(\nu,\mathbb P)$ and write $\rho=\frac{rp}{r+p}$, $\delta=\kappa-\theta$ and
--   $$\bar V^\nu:=\mathbb E^{\mathbb P}\Big[-e^{-\rho\left(\int_0^T(\delta X_t-c(\nu_t))dt-\frac h2\langle X\rangle_T\right)}\Big].$$
--   If $\bar V^\nu=w$ for a real number $w<0$, then there is a contract $\xi\in\mathcal C$ (satisfying the integrability condition (2.5)) with $J_A(\xi,\mathbb P^\nu)\ge R_0$ and
--   $$J_P(\xi,\mathbb P^\nu)=R_0\Big(\frac{w}{R_0}\Big)^{1+\frac pr}.$$
--
--   This is the attainment half of the Lagrangian reduction (A.3)–(A.5): the contract is the first-order-condition payment (A.4),
--   $$\xi_\ell=\frac1{p+r}\ln\frac{r\ell}{p}-\frac{p}{p+r}G^\nu_T-\frac{r}{p+r}K^\nu_T,$$
--   with the multiplier $\ell^\star$ of (A.5) computed from $w$, where $K^\nu_T=\int_0^T(\kappa X_s-c(\nu_s))ds$ and $G^\nu_T=\int_0^T\theta X_sds+\frac h2\langle X\rangle_T$. Substituting it makes the participation constraint bind and gives the stated producer value. The non-trivial part is that $\xi_{\ell^\star}$ belongs to $\mathcal C$, i.e. has uniformly bounded exponential moments over all admissible pairs.
--
--   **Formalization Note** $\langle X\rangle_T$ is its almost-sure value $\int_0^T|\sigma(\beta_t)|^2dt$ under the admissible pair, as in the definitions of $J_P$ and $\bar V$. Only the existence of an optimal contract is stated, not its explicit form.
-- source:
--   arXiv:1810.09063v3 (Aïd, Possamaï, Touzi), Appendix A.2, proof of Proposition 3.1, equations (A.3)–(A.5), p. 26

import Mathlib
import Definitions.Def_DemandResponse_FirstBest_Model

open MeasureTheory

namespace DemandResponse.FirstBest

/-- (A.4)–(A.5), attainment for a fixed effort: if `(ν, ℙ)` is admissible and the reduced
criterion `-E^ℙ[exp(-ρ(∫₀ᵀ (δ X_t - c(ν_t)) dt - (h/2)⟨X⟩_T))]` equals the real `w < 0`, then
some contract `ξ ∈ 𝒞` (the Lagrangian contract (A.4) with the optimal multiplier) satisfies the
participation constraint and gives the producer `J_P(ξ, ℙ^ν) = R₀ (w / R₀)^{1 + p/r}`. -/
theorem eqA4_optimal_contract_attains {N d : ℕ} (P : Params N d)
    (ν : Control P) (Q : Measure (Path P)) (hQ : Admissible P ν Q) (w : ℝ) (hw : w < 0)
    (hCw : -(((∫⁻ ω, ENNReal.ofReal (Real.exp (-rho P *
      ((∫ s in (0 : ℝ)..P.T, (delta P * Xr P s ω - cost P (ν.αr s ω) (ν.βr s ω))) -
        P.h / 2 * qvInt P ν P.T ω))) ∂Q) : ENNReal) : EReal) = (w : EReal)) :
    ∃ ξ : Path P → ℝ, IsContract P ξ ∧ (P.R₀ : EReal) ≤ JA P ξ ν Q ∧
      JP P ξ ν Q = ((P.R₀ * (w / P.R₀) ^ (1 + P.p / P.r) : ℝ) : EReal) := by sorry

end DemandResponse.FirstBest
