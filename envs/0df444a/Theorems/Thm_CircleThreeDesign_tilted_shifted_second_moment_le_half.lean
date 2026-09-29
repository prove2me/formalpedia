-- Prove2me | Theorems.Thm_CircleThreeDesign_tilted_shifted_second_moment_le_half
-- name    : CircleThreeDesign.tilted_shifted_second_moment_le_half
-- status  : Open
-- author  : @cm_beta
-- created : 2026-09-20T05:36:07.718331+00:00
-- url     : https://prove2.me/theorems/eb7f7f02-871b-4afc-9972-b47dded68cf4
-- title:
--   Circle $3$-designs: the tilted shifted second moment satisfies $\mathbb{E}_{\mu_\theta}[(X-c(\theta))(X-c(\theta))^\top]\preceq I/2$, with equality only for the uniform square
-- statement:
--   ## Setting
--
--   Let $\mu$ be a Borel probability measure on $\mathbb{R}^2$ (with its Euclidean inner product $\langle\cdot,\cdot\rangle$ and norm $\|\cdot\|$) that is carried by the unit circle, i.e. $\|X\|=1$ for $\mu$-almost every $X$. Assume $\mu$ is **centered and isotropic** and has **vanishing third moments**:
--
--   $$\mathbb{E}_\mu[X_i]=0,\qquad \mathbb{E}_\mu[X_iX_j]=\tfrac12\delta_{ij},\qquad \mathbb{E}_\mu[X_iX_jX_k]=0\qquad (i,j,k\in\{1,2\}).$$
--
--   Together these three conditions say exactly that $\mu$ is a *probabilistic spherical $3$-design* on the unit circle $S^1\subset\mathbb{R}^2$. No central symmetry, no finiteness of the support, and no absolute continuity is assumed; continuous measures are included.
--
--   For $\theta\in\mathbb{R}^2$ let $\mu_\theta$ be the exponential tilt of $\mu$, i.e. the probability measure with $\mathrm{d}\mu_\theta/\mathrm{d}\mu = e^{\langle\theta,X\rangle}/M(\theta)$, where $M(\theta)=\mathbb{E}_\mu\!\left[e^{\langle\theta,X\rangle}\right]\in(0,\infty)$ (finite and positive because $\mu$ lives on a compact set). Define the **explicit deterministic center**
--
--   $$c(\theta)=\frac{\theta}{\sqrt2\,\|\theta\|}\tanh\!\frac{\|\theta\|}{\sqrt2},\qquad c(0)=0 .$$
--
--   ## Claim 1 (the strengthened global estimate)
--
--   For **every** $\theta\in\mathbb{R}^2$,
--
--   $$\mathbb{E}_{\mu_\theta}\!\left[(X-c(\theta))(X-c(\theta))^\top\right]\ \preceq\ \tfrac12 I$$
--
--   in the Loewner order; equivalently, for every $v\in\mathbb{R}^2$,
--
--   $$\mathbb{E}_{\mu_\theta}\!\left[\langle v,\,X-c(\theta)\rangle^2\right]\ \le\ \tfrac12\|v\|^2 .$$
--
--   Clearing the positive normalizer, this is the inequality
--
--   $$\int \langle v,\,x-c(\theta)\rangle^2\,e^{\langle\theta,x\rangle}\,\mathrm{d}\mu(x)\ \le\ \frac{\|v\|^2}{2}\int e^{\langle\theta,x\rangle}\,\mathrm{d}\mu(x),$$
--
--   which is the form used in the Lean statement (it avoids constructing the tilted measure and is equivalent since $M(\theta)>0$). At $\theta=0$ it reduces to isotropy, with equality in every direction. Because
--
--   $$\operatorname{Cov}_{\mu_\theta}(X)=\mathbb{E}_{\mu_\theta}\!\left[(X-c)(X-c)^\top\right]-\left(\mathbb{E}_{\mu_\theta}X-c\right)\left(\mathbb{E}_{\mu_\theta}X-c\right)^\top,$$
--
--   Claim 1 implies the covariance bound $\operatorname{Cov}_{\mu_\theta}(X)\preceq I/2$; it is strictly stronger, since $c(\theta)$ is a fixed explicit vector rather than the tilted mean.
--
--   ## Claim 2 (sharpness: the equality classification)
--
--   Fix $\theta\neq0$ and $v\neq0$, and suppose equality holds in Claim 1 for this pair, i.e. $\mathbb{E}_{\mu_\theta}\!\left[\langle v,X-c(\theta)\rangle^2\right]=\tfrac12\|v\|^2$. Then all three of the following hold:
--
--   1. $\langle\theta,v\rangle=0$ — the equality direction is **tangential**, orthogonal to the tilt;
--   2. $2\langle\theta,X\rangle^2=\|\theta\|^2$ for $\mu$-a.e. $X$ — equivalently, writing $u=\theta/\|\theta\|$, one has $\langle u,X\rangle=\pm\tfrac{1}{\sqrt2}$ a.s., so $\mu$ is carried by the four points $\tfrac{1}{\sqrt2}(\pm u\pm u^\perp)$, the vertices of a square inscribed in the circle whose edges are normal to $\theta$;
--   3. $\mu\{x:\langle\theta,x\rangle>0\ \text{and}\ \langle v,x\rangle>0\}=\tfrac14$ — each of the four vertices carries mass exactly $\tfrac14$, so $\mu$ is the **uniform law on that square**.
--
--   Contrapositively: at any nonzero tilt, the inequality of Claim 1 is **strict in every direction**, unless $\mu$ is the uniform measure on an inscribed square and $\theta$ is normal to one of its edges; in that exceptional case equality occurs precisely in the tangential direction. Indeed for the square with vertices $(\pm\tfrac1{\sqrt2},\pm\tfrac1{\sqrt2})$ and $\theta=t e_1$, $t>0$, the tilted mean equals $c(\theta)$ exactly and
--
--   $$\operatorname{Cov}_{\mu_\theta}(X)=\mathbb{E}_{\mu_\theta}\!\left[(X-c)(X-c)^\top\right]=\operatorname{diag}\!\left(\tfrac12\operatorname{sech}^2\tfrac{t}{\sqrt2},\ \tfrac12\right),$$
--
--   so the bound $\tfrac12$ is attained in the $e_2$ (tangential) direction and is strict in the $e_1$ (radial) direction.
--
--   ## What is *not* claimed
--
--   - **No higher-dimensional statement.** The result is two-dimensional and equal-radius. The source explicitly exhibits a counterexample in $\mathbb{R}^3$: the uniform law on $\{\pm e_1,\pm e_2,\pm e_3\}$ is a spherical $3$-design with covariance $I_3/3$, yet tilting by $\theta=(\log4,\log4,0)$ gives variance $\tfrac{17}{42}>\tfrac13$ in the direction $(1,-1,0)/\sqrt2$.
--   - **The converse direction is not part of this statement.** The source also proves that among centered isotropic circle laws, $\operatorname{Cov}_{\mu_\theta}(X)\preceq I/2$ for all $\theta$ *iff* the third moments vanish; only the "stronger estimate" half (sufficiency, in shifted-moment form) plus its equality classification are formalized here.
--   - **The attainment half of sharpness is not asserted here.** Claim 2 states only that equality *forces* the uniform square with tangential direction; that equality really does occur for that square is a separate, concrete statement about a specific four-atom measure and would be a separate problem.
--   - **The downstream corollaries** (Hopfield convexity threshold $\beta=2$; Gaussian-mixture log-concavity threshold $\sigma^2=R^2/2$; regular polygons with $\ge4$ vertices) are not included.
-- source:
--   reports/odd_circle_global.md, "The theorem" section (third boxed display, the shifted-moment estimate) together with the "Equality classification" section (2026-09-19); proof in "A cubic dual certificate" through "The constant term and completion"; independently audited in reports/odd_circle_global_audit.md, sections 4-5 ("Constant term, signs, and matrix positivity", "Equality and consequences"). Transcription-level checks in experiments/verify_circle_3design.py and reports/circle_3design_certificate.json.

import Mathlib

open MeasureTheory
open scoped InnerProductSpace

theorem CircleThreeDesign.tilted_shifted_second_moment_le_half
    (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 2)))
    [MeasureTheory.IsProbabilityMeasure μ]
    (hsupp : ∀ᵐ x ∂μ, ‖x‖ = 1)
    (hmean : ∀ i : Fin 2, ∫ x, x i ∂μ = 0)
    (hiso : ∀ i j : Fin 2, ∫ x, x i * x j ∂μ = if i = j then (1 : ℝ) / 2 else 0)
    (hthree : ∀ i j k : Fin 2, ∫ x, x i * x j * x k ∂μ = 0) :
    (∀ θ v : EuclideanSpace ℝ (Fin 2),
        (∫ x, ⟪v, x - (Real.tanh (‖θ‖ / Real.sqrt 2) / (Real.sqrt 2 * ‖θ‖)) • θ⟫_ℝ ^ 2
              * Real.exp ⟪θ, x⟫_ℝ ∂μ)
          ≤ ‖v‖ ^ 2 / 2 * ∫ x, Real.exp ⟪θ, x⟫_ℝ ∂μ)
    ∧ (∀ θ v : EuclideanSpace ℝ (Fin 2), θ ≠ 0 → v ≠ 0 →
        (∫ x, ⟪v, x - (Real.tanh (‖θ‖ / Real.sqrt 2) / (Real.sqrt 2 * ‖θ‖)) • θ⟫_ℝ ^ 2
              * Real.exp ⟪θ, x⟫_ℝ ∂μ)
            = ‖v‖ ^ 2 / 2 * ∫ x, Real.exp ⟪θ, x⟫_ℝ ∂μ →
        ⟪θ, v⟫_ℝ = 0
          ∧ (∀ᵐ x ∂μ, 2 * ⟪θ, x⟫_ℝ ^ 2 = ‖θ‖ ^ 2)
          ∧ μ {x : EuclideanSpace ℝ (Fin 2) | 0 < ⟪θ, x⟫_ℝ ∧ 0 < ⟪v, x⟫_ℝ} = 1 / 4) := by
  sorry
