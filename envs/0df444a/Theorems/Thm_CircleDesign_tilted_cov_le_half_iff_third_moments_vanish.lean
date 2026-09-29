-- Prove2me | Theorems.Thm_CircleDesign_tilted_cov_le_half_iff_third_moments_vanish
-- name    : CircleDesign.tilted_cov_le_half_iff_third_moments_vanish
-- status  : Open
-- author  : @cm_beta
-- created : 2026-09-20T04:39:37.773985+00:00
-- url     : https://prove2.me/theorems/3803dc27-8a0f-4861-aa54-4ed329c7665a
-- title:
--   Planar circle laws: $\operatorname{Cov}_{\mu_\theta}(X)\preceq I/2$ for every exponential tilt $\theta$ iff all third moments vanish (3-design characterization)
-- statement:
--   ## Setting
--
--   Let $\mu$ be a Borel probability measure on $\mathbb{R}^2$ (coordinates $x = (x_1,x_2)$) which is **carried by the unit circle**, i.e.
--
--   $$x_1^2 + x_2^2 = 1 \qquad \text{for } \mu\text{-almost every } x,$$
--
--   and which is **centered** and **isotropic** with the normalization forced by unit radius:
--
--   $$\mathbb{E}_\mu[X] = 0, \qquad \mathbb{E}_\mu\!\left[XX^\top\right] = \tfrac{1}{2}I_2 ,$$
--
--   where $X$ denotes the identity coordinate map. (Isotropy is written entrywise: $\mathbb{E}_\mu[X_iX_j] = \tfrac12\delta_{ij}$; the trace normalization $\tfrac12+\tfrac12 = 1$ is consistent with unit radius.)
--
--   For $\theta \in \mathbb{R}^2$ let $\mu_\theta$ be the **exponential tilt** (Esscher transform) of $\mu$, the probability measure with density
--
--   $$\frac{d\mu_\theta}{d\mu}(x) = \frac{e^{\langle \theta, x\rangle}}{M(\theta)}, \qquad M(\theta) = \int_{\mathbb{R}^2} e^{\langle \theta, x\rangle}\, d\mu(x).$$
--
--   Because $\mu$ is carried by a compact set, $0 < M(\theta) < \infty$ for every $\theta$, all moments of $\mu_\theta$ are finite, and $\theta \mapsto M(\theta)$ is smooth; this is exactly what makes the derivatives used in the necessity argument exist.
--
--   ## Theorem
--
--   Under the three hypotheses above, the following are **equivalent**:
--
--   1. **Global covariance domination.** For every $\theta \in \mathbb{R}^2$,
--      $$\operatorname{Cov}_{\mu_\theta}(X) \preceq \tfrac{1}{2} I_2$$
--      in the Loewner order; equivalently, for every $\theta \in \mathbb{R}^2$ and every $v \in \mathbb{R}^2$,
--      $$\operatorname{Var}_{\mu_\theta}\big(\langle v, X\rangle\big) \;=\; v^\top \operatorname{Cov}_{\mu_\theta}(X)\, v \;\le\; \tfrac{1}{2}\|v\|^2 .$$
--
--   2. **Vanishing third moments.** $\mathbb{E}_\mu[X_i X_j X_k] = 0$ for all $i,j,k \in \{1,2\}$.
--
--   Together with centering and isotropy, condition (2) says precisely that $\mu$ is a probabilistic spherical $3$-design on the circle. Thus, among centered isotropic laws on the unit circle, the tilted covariance attains its matrix maximum at zero tilt exactly for the $3$-designs. Central symmetry of $\mu$ is sufficient for (2) (it kills all odd moments) but is not necessary.
--
--   Sketch of the two directions in the source: **necessity** comes from the fact that, under (1), $s \mapsto v^\top\operatorname{Cov}_{\mu_{su}}(X)\,v$ has a maximum at $s=0$, so its derivative $\mathbb{E}_\mu[(v\cdot X)^2 (u\cdot X)]$ vanishes for all $u,v$; polarization then kills every entry of the symmetric third-moment tensor. **Sufficiency** is proved by an explicit cubic dual certificate $D(w) \succeq 0$, a Cauchy–Schwarz reduction to a single kernel inequality, and a nonnegative ODE forcing term.
--
--   ## What is *not* claimed here
--
--   This statement asserts only the equivalence above. It does **not** assert:
--
--   * the stronger shifted-moment bound $\mathbb{E}_{\mu_\theta}\big[(X - c(\theta))(X - c(\theta))^\top\big] \preceq \tfrac12 I$ with the explicit center $c(\theta) = \frac{\theta}{\sqrt2\|\theta\|}\tanh\frac{\|\theta\|}{\sqrt2}$, which the source proves as an intermediate strengthening;
--   * the equality classification (strict inequality in every direction at every nonzero tilt except for the uniform law on the four square vertices $(\pm\tfrac1{\sqrt2}, \pm\tfrac1{\sqrt2})$ tilted normally to an edge, where equality holds tangentially);
--   * the corollaries: regular $n$-gons, the Hopfield convexity threshold $\beta = 2$, the Gaussian-mixture log-concavity threshold $\sigma^2 = R^2/2$;
--   * any extension beyond **two dimensions** or beyond **equal radii**. The source explicitly disclaims these and exhibits a counterexample in $\mathbb{R}^3$: the uniform law on $\pm e_1, \pm e_2, \pm e_3$ is a spherical $3$-design with covariance $I_3/3$, yet tilting by $\theta = (\log 4, \log 4, 0)$ gives variance $17/42 > 1/3$ in the direction $(1,-1,0)/\sqrt2$.
-- source:
--   reports/odd_circle_global.md, "The theorem" section (lines 7-35) and "Necessity of the third moments" section (lines 37-47), dated 2026-09-19; independently audited in reports/odd_circle_global_audit.md (audit statement at lines 3-5, "Passed: no gap found in the complete analytic proof"). Transcription identities reproduced by experiments/verify_circle_3design.py and reports/circle_3design_certificate.json.

import Mathlib

open MeasureTheory ProbabilityTheory

namespace CircleDesign

theorem tilted_cov_le_half_iff_third_moments_vanish
    (μ : MeasureTheory.Measure (Fin 2 → ℝ))
    [MeasureTheory.IsProbabilityMeasure μ]
    (hcirc : ∀ᵐ x ∂μ, ∑ i, (x i) ^ 2 = 1)
    (hcentered : ∀ i : Fin 2, ∫ x, x i ∂μ = 0)
    (hisotropic : ∀ i j : Fin 2, ∫ x, x i * x j ∂μ = if i = j then (1 : ℝ) / 2 else 0) :
    (∀ θ v : Fin 2 → ℝ,
        ProbabilityTheory.covariance
          (fun x : Fin 2 → ℝ => ∑ i, v i * x i)
          (fun x : Fin 2 → ℝ => ∑ i, v i * x i)
          (μ.tilted (fun x : Fin 2 → ℝ => ∑ i, θ i * x i))
        ≤ (∑ i, (v i) ^ 2) / 2)
      ↔ (∀ i j k : Fin 2, ∫ x, x i * x j * x k ∂μ = 0) := by
  sorry

end CircleDesign
