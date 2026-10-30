-- Prove2me | Theorems.Thm_DDROCS_eq_34_worst_case_var_bound
-- name    : DDROCS.eq_34_worst_case_var_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T23:33:13.658003+00:00
-- url     : https://prove2.me/theorems/072bf04c-217a-4b53-9a73-02d50b8aa4b9
-- title:
--   Eq. (34): worst-case VaR over $\mathcal P^{CS}$ is bounded by $\hat\mu^\top v + \Gamma_1\|v\|_2 + \sqrt{(1-\epsilon)/\epsilon}\sqrt{v^\top(\hat\Sigma+\Gamma_2 I)v}$ (corrected: ≤ in place of =)
-- statement:
--   Let $R, \Gamma_1, \Gamma_2 \in \mathbb R$, $\hat\mu \in \mathbb R^d$ and $\hat\Sigma \in \mathbb R^{d\times d}$, and let $\mathcal P^{CS}$ be the Shawe-Taylor–Cristianini region built from them. Then for every $\mathbb P \in \mathcal P^{CS}$, every $0<\epsilon<1$ and every $v \in \mathbb R^d$,
--
--   $$
--   \mathrm{VaR}^{\mathbb P}_\epsilon(v) \;\le\; \hat\mu^\top v + \Gamma_1\|v\|_2 + \sqrt{\frac{1-\epsilon}{\epsilon}}\,\sqrt{v^\top(\hat\Sigma + \Gamma_2 I)v},
--   $$
--
--   that is, $\sup_{\mathbb P \in \mathcal P^{CS}} \mathrm{VaR}^{\mathbb P}_\epsilon(v)$ is at most the right-hand side.
--
--   This is Step 2 of the paper's schema for the confidence region $\mathcal P^{CS}$: a convex, positively homogeneous upper bound on the worst-case Value at Risk. Its right-hand side is the support function of the set $\mathcal U^{CS}_\epsilon$ of (35), which is how Theorem 10 follows from Theorem 3.
--
--   Differences from the source:
--   - correction: sup_{P∈P^CS} VaR^P_ϵ(v) = µ̂ᵀv + Γ1‖v‖2 + √((1 − ϵ)/ϵ) √(vᵀ(Σ̂ + Γ2 I)v) → VaR P ε v ≤ the same right-hand side for every P ∈ P^CS; reason: every P ∈ P^CS is supported in the ball of radius R, so the left side is at most R‖v‖; with d = 1, R = 1, N = 100, α = 0.1, Theorem 9's thresholds Γ1 ≈ 0.4448, Γ2 ≈ 0.9432, an all-zero sample (µ̂ = 0, Σ̂ = 0, so the Dirac mass at 0 lies in P^CS), v = 1, ϵ = 0.01, the left side is at most 1 and the right side is about 10.1; ≤ is the direction used by Step 2 and the proof of Theorem 10
--   - generalization: µ̂, Σ̂ the sample mean and covariance and Γ1, Γ2 the thresholds of Theorem 9 or of the bootstrap → arbitrary µ̂ ∈ ℝ^d, Σ̂ ∈ ℝ^{d×d}, R, Γ1, Γ2 ∈ ℝ; reason: the bound holds for any centre, matrix and thresholds, and specializes to the paper's choices
--   - reading: Θ(R) the Borel probability measures supported on the ball of radius R → probability measures P with P(closed ball of radius R about 0) = 1; reason: a support is closed, and the ball of Theorem 9 is centred at the origin
--   - encoding: supremum over P ∈ P^CS → the bound for every P ∈ P^CS; reason: a supremum is at most c exactly when every member is at most c
--   - encoding: level ϵ (the schema's 0 < ϵ < 1, p. 10) → hypotheses 0 < ε and ε < 1; reason: the paper's range written as binders
-- source:
--   Bertsimas, Gupta, Kallus, Data-Driven Robust Optimization, arXiv:1401.0212v2, eq. (34), p. 25

import Mathlib
import Definitions.Def_DDROCS_VaR
import Definitions.Def_DDROCS_PCS
open MeasureTheory InnerProductSpace

namespace DDROCS

/-- **Eq. (34), corrected to "≤": worst-case VaR over `P^CS`.**
Bertsimas, Gupta, Kallus, Data-Driven Robust Optimization, arXiv:1401.0212v2, eq. (34), p. 25:
"Bounding Value at Risk for regions like `P^CS` was studied by Calafiore and El Ghaoui (2006).
Their results imply `sup_{P∈P^CS} VaR^P_ϵ(v) = µ̂ᵀv + Γ1‖v‖2 + √((1 − ϵ)/ϵ) √(vᵀ(Σ̂ + Γ2 I)v)`."

For every `P ∈ P^CS`, every `0 < ε < 1` and every `v`,
`VaR^P_ε(v) ≤ µ̂ᵀv + Γ₁‖v‖₂ + √((1 − ε)/ε) √(vᵀ(Σ̂ + Γ₂ I)v)`, i.e. the supremum over `P^CS`
is at most the right-hand side.

**Formalization Note.** *Correction.* The printed equality is false: every `P ∈ P^CS` is
supported in the ball of radius `R`, so the left side is at most `R‖v‖`, while the right side can
be larger (`d = 1`, `R = 1`, `N = 100`, `α = 0.1`, Theorem 9's thresholds `Γ₁ ≈ 0.4448`,
`Γ₂ ≈ 0.9432`, all-zero sample so `µ̂ = 0`, `Σ̂ = 0` and the Dirac mass at `0` lies in `P^CS`,
`v = 1`, `ε = 0.01`: left side `≤ 1`, right side `≈ 10.1`). The inequality `≤` is the direction
that Step 2 of the schema and the proof of Theorem 10 use. The supremum over `P^CS` is stated
pointwise in `P`. `µ̂`, `Σ̂`, `R`, `Γ₁`, `Γ₂` are arbitrary reals/vectors/matrices (the sample mean
and covariance and the thresholds of Theorem 9 or of the bootstrap are instances). `vᵀAv` is
`∑ i, ∑ j, v i * A i j * v j`, `µ̂ᵀv` the Euclidean inner product, `‖v‖₂` the Euclidean norm. -/
theorem eq_34_worst_case_var_bound {d : ℕ} (R : ℝ) (μhat : EuclideanSpace ℝ (Fin d))
    (Sigmahat : Matrix (Fin d) (Fin d) ℝ) (Γ₁ Γ₂ : ℝ)
    (P : Measure (EuclideanSpace ℝ (Fin d))) (hP : P ∈ PCS R μhat Sigmahat Γ₁ Γ₂)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (v : EuclideanSpace ℝ (Fin d)) :
    VaR P ε v ≤ ⟪μhat, v⟫_ℝ + Γ₁ * ‖v‖ + Real.sqrt ((1 - ε) / ε) *
      Real.sqrt (∑ i, ∑ j, v i * (Sigmahat + Γ₂ • (1 : Matrix (Fin d) (Fin d) ℝ)) i j * v j) := by sorry

end DDROCS
