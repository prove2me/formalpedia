-- Prove2me | Theorems.Thm_CircleDesign_gaussian_mixture_logConcave_iff_three_design
-- name    : CircleDesign.gaussian_mixture_logConcave_iff_three_design
-- status  : Open
-- author  : @cm_beta
-- created : 2026-09-20T04:45:26.798985+00:00
-- url     : https://prove2.me/theorems/689f8c92-d08a-466c-bc33-c215de764653
-- title:
--   Gaussian smoothing of a planar circular $3$-design is log-concave exactly when $\sigma^2 \ge R^2/2$
-- statement:
--   Fix a radius $R>0$ and let $\nu$ be a Borel probability measure on the plane $\mathbb R^2$ that is carried by the circle of radius $R$, that is,
--   $$y_1^2+y_2^2=R^2\qquad\text{for }\nu\text{-almost every }y=(y_1,y_2).$$
--   Assume that $\nu$ is **centered** and **isotropic**:
--   $$\int y_1\,d\nu=\int y_2\,d\nu=0,\qquad \int y_1^2\,d\nu=\int y_2^2\,d\nu=\frac{R^2}{2},\qquad \int y_1y_2\,d\nu=0.$$
--
--   Say that $\nu$ satisfies the **third-moment condition** when all four cubic moments vanish,
--   $$\int y_1^3\,d\nu=\int y_1^2y_2\,d\nu=\int y_1y_2^2\,d\nu=\int y_2^3\,d\nu=0.$$
--   Together with centering and isotropy this says exactly that $\nu$ is a probabilistic spherical $3$-design on the radius-$R$ circle; the equal-weight uniform measure on the vertices of any regular $n$-gon with $n\ge4$ is an example, but central symmetry is not required.
--
--   For $\sigma>0$ let $p_\sigma$ be the density of the Gaussian mixture $\nu * N(0,\sigma^2I_2)$, namely
--   $$p_\sigma(x)=\int_{\mathbb R^2}\frac{1}{2\pi\sigma^2}\exp\!\left(-\frac{\lVert x-y\rVert^2}{2\sigma^2}\right)d\nu(y),\qquad x\in\mathbb R^2 .$$
--   This function is everywhere positive and smooth, so *log-concavity* of $p_\sigma$ means concavity of $\log p_\sigma$ on all of $\mathbb R^2$.
--
--   The assertion has two parts.
--
--   1. **Sharp variance threshold for $3$-designs.** If $\nu$ satisfies the third-moment condition, then for every $\sigma>0$
--   $$p_\sigma\ \text{is log-concave}\iff \sigma^2\ \ge\ \frac{R^2}{2}.$$
--
--   2. **Characterization at the critical variance.** If $\sigma>0$ and $\sigma^2=R^2/2$, then
--   $$p_\sigma\ \text{is log-concave}\iff \nu\ \text{satisfies the third-moment condition}.$$
--
--   Equal radii are what make this exact. Because $\lVert y\rVert$ is $\nu$-a.s. constant, the Gaussian quadratic reweighting of the mixing law is constant on the support, and the log-density Hessian is
--   $$\nabla^2\log p_\sigma(x)=-\frac{1}{\sigma^2}I_2+\frac{1}{\sigma^4}\operatorname{Cov}_{\nu_{x/\sigma^2}}(X),$$
--   where $\nu_\theta$ is the exponential tilt of $\nu$ with density proportional to $e^{\theta\cdot y}$. Log-concavity of $p_\sigma$ is therefore the same as the uniform tilted-covariance bound $\operatorname{Cov}_{\nu_\theta}(X)\preceq\sigma^2I_2$ for all $\theta\in\mathbb R^2$, in the Loewner order. The content of the statement is that among centered isotropic laws on a fixed circle this bound at the *smallest possible* variance $\sigma^2=R^2/2$ holds precisely for the $3$-designs; the value $R^2/2$ cannot be lowered, since at $x=0$ the Hessian already forces $\sigma^2\ge R^2/2$. The result gives a sharp, checkable smoothing criterion for two-dimensional equal-radius mixtures, and it is the Gaussian-convolution face of the corresponding convexity threshold for weighted planar Hopfield energies.
--
--   **Scope of the claim.** This is a two-dimensional, equal-radius statement, and nothing beyond that is asserted. No arbitrary-dimensional and no unequal-radius version is claimed, and the dimension restriction is essential rather than technical: the uniform law on $\{\pm e_1,\pm e_2,\pm e_3\}\subset\mathbb R^3$ is a spherical $3$-design with covariance $I_3/3$, yet tilting by $\theta=(\log4,\log4,0)$ gives variance $\tfrac{17}{42}>\tfrac13$ in the direction $(1,-1,0)/\sqrt2$, so vanishing third moments does not yield the analogous domination in dimension three. Part 2 is also asserted only at the critical variance: larger smoothing variances do *not* characterize $3$-designs, and no claim is made about them beyond part 1. Finally, no statement is made here about strict log-concavity, about the equality cases, or about mixing laws whose mass is spread over several radii.
--
--   **Formalization Note.** Mathlib has no predicate for log-concavity or for spherical designs, so both are written out: log-concavity is `ConcaveOn ℝ Set.univ (fun x => Real.log (p σ x))`, and the design condition is the explicit list of the four cubic moment integrals. The plane is modelled as `ℝ × ℝ` with all Euclidean quantities written in coordinates, so that the sup-norm on the product type is never used. The mixture density is introduced as a function variable `p` pinned by the defining hypothesis `hp` rather than by a local definition. All the integrands are measurable and $\nu$-a.e. bounded on the circle, so every integral appearing in the hypotheses and in `hp` is genuinely convergent and no junk value of the Bochner integral is involved.
-- source:
--   reports/odd_circle_global.md, section "Consequences and scope", bullet "Gaussian mixtures" (line 255) together with the scope paragraph at line 257 ("These are two-dimensional equal-radius results. No arbitrary-dimensional or unequal-radius extension is asserted."); the underlying equivalence is the boxed statement in the section "The theorem" (lines 9-23) of the same file. Dated 2026-09-19. Audited in reports/odd_circle_global_audit.md, section 5 ("a radius-R>0 circle 3-design mixture has Gaussian log-concavity threshold sigma^2=R^2/2 ... Equal radius and two-dimensional circle support are essential stated hypotheses"). The Hessian identity and the critical-variance reading are recorded in reports/circle_3design_prior_art.md, section "Exact Gaussian-convolution consequence and its scope".

import Mathlib

open MeasureTheory Filter Topology

namespace CircleDesign

theorem gaussian_mixture_logConcave_iff_three_design
    (R : ℝ) (hR : 0 < R)
    (ν : Measure (ℝ × ℝ)) [IsProbabilityMeasure ν]
    (hsupp : ∀ᵐ y ∂ν, y.1 ^ 2 + y.2 ^ 2 = R ^ 2)
    (hmean1 : ∫ y, y.1 ∂ν = 0)
    (hmean2 : ∫ y, y.2 ∂ν = 0)
    (hcov11 : ∫ y, y.1 ^ 2 ∂ν = R ^ 2 / 2)
    (hcov22 : ∫ y, y.2 ^ 2 ∂ν = R ^ 2 / 2)
    (hcov12 : ∫ y, y.1 * y.2 ∂ν = 0)
    (p : ℝ → ℝ × ℝ → ℝ)
    (hp : ∀ σ : ℝ, ∀ x : ℝ × ℝ, p σ x =
      ∫ y, (2 * Real.pi * σ ^ 2)⁻¹ *
        Real.exp (-((x.1 - y.1) ^ 2 + (x.2 - y.2) ^ 2) / (2 * σ ^ 2)) ∂ν) :
    ((∫ y, y.1 ^ 3 ∂ν = 0 ∧ ∫ y, y.1 ^ 2 * y.2 ∂ν = 0 ∧
        ∫ y, y.1 * y.2 ^ 2 ∂ν = 0 ∧ ∫ y, y.2 ^ 3 ∂ν = 0) →
      ∀ σ : ℝ, 0 < σ →
        (ConcaveOn ℝ (Set.univ : Set (ℝ × ℝ)) (fun x => Real.log (p σ x)) ↔
          R ^ 2 / 2 ≤ σ ^ 2))
    ∧
    (∀ σ : ℝ, 0 < σ → σ ^ 2 = R ^ 2 / 2 →
      (ConcaveOn ℝ (Set.univ : Set (ℝ × ℝ)) (fun x => Real.log (p σ x)) ↔
        (∫ y, y.1 ^ 3 ∂ν = 0 ∧ ∫ y, y.1 ^ 2 * y.2 ∂ν = 0 ∧
          ∫ y, y.1 * y.2 ^ 2 ∂ν = 0 ∧ ∫ y, y.2 ^ 3 ∂ν = 0))) := by sorry

end CircleDesign
