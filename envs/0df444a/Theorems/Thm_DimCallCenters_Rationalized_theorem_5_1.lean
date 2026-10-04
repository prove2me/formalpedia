-- Prove2me | Theorems.Thm_DimCallCenters_Rationalized_theorem_5_1
-- name    : DimCallCenters.Rationalized.theorem_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T10:35:00.136965+00:00
-- url     : https://prove2.me/theorems/2c3a1a7c-8625-4293-84f4-ef5947288842
-- title:
--   Theorem 5.1 — the rationalized staffing function $y^*_\lambda$ is asymptotically optimal
-- statement:
--   Assume the standing assumptions of Section 2 on $(\mu, D_\lambda)$, and let the staffing cost $F$ be convex and strictly increasing on $(0,\infty)$. Assume moreover that $G(N,\lambda) \to \infty$ as $N \downarrow \lambda/\mu$, for every $\lambda>0$. Suppose the regime is **rationalized**, (18): for some $\kappa > 0$,
--
--   $$\lim_{\lambda\to\infty}\frac{F_\lambda(\kappa)}{G_\lambda(\kappa)} = \gamma \in (0,\infty).$$
--
--   For every $\lambda > 0$ let $y^*_\lambda > 0$ minimize $F_\lambda(y) + P(y)\,G_\lambda(y)$ over $y > 0$, (19), and let $N^*_\lambda$ be an optimal integer staffing level, (7). Then
--
--   $$\lim_{\lambda\to\infty}\frac{S_\lambda(y^*_\lambda) - F(\lambda/\mu)}{C(N^*_\lambda,\lambda) - F(\lambda/\mu)} = 1,$$
--
--   i.e. staffing at the cheaper integer next to $\lambda/\mu + y^*_\lambda\sqrt{\lambda/\mu}$ is asymptotically optimal in the sense of Corollary 3.3. This is the theorem behind the square-root safety-staffing rule $N \approx R + y^*\sqrt R$, $R = \lambda/\mu$.
--
--   **Formalization Note** The hypothesis $\lim_{N\downarrow\lambda/\mu} G(N,\lambda) = \infty$ is asserted by the paper on p. 12 but does not follow from its standing assumptions (for bounded $D_\lambda$ the limit is finite); it is equivalent to $D_\lambda$ being unbounded and is needed for the continuous optimum $x^*_\lambda$ used in the proof to exist. The minimizers $y^*_\lambda$ and $N^*_\lambda$ are hypotheses (any minimizer). $S_\lambda$ omits the floor term when the floor is not a stable level.
-- source:
--   Borst, Mandelbaum & Reiman, Dimensioning Large Call Centers, CWI Report PNA-R0015 (2000), p. 17, Theorem 5.1 (with Section 5 preamble, Eqs. (18)-(19), p. 16-17)

import Mathlib
import Definitions.Def_DimCallCenters_Rationalized_Flam
import Definitions.Def_DimCallCenters_Rationalized_Glam
import Definitions.Def_DimCallCenters_Rationalized_surrogate
import Definitions.Def_DimCallCenters_Rationalized_delayFn
import Definitions.Def_DimCallCenters_Rationalized_staffCost

open Filter Topology

namespace DimCallCenters.Rationalized

/-- Theorem 5.1 (p. 17). In the rationalized regime (18) — `F_λ(κ)/G_λ(κ) → γ ∈ (0, ∞)` for some
`κ > 0` — the staffing function `y*_λ = argmin_{y>0} F_λ(y) + P(y) G_λ(y)` (19) is asymptotically
optimal: `S_λ(y*_λ) - F(λ/μ) ≈ C(N*_λ, λ) - F(λ/μ)` as `λ → ∞`. The hypothesis `hGinf`
(`G(N, λ) → ∞` as `N ↓ λ/μ`) is asserted on p. 12 of the paper but does not follow from its
standing assumptions; it is added here. -/
theorem theorem_5_1 (M : WaitModel) (F : ℝ → ℝ)
    (hFconv : ConvexOn ℝ (Set.Ioi 0) F) (hFmono : StrictMonoOn F (Set.Ioi 0))
    (hGinf : ∀ lam : ℝ, 0 < lam →
      Tendsto (fun N => waitCost M N lam) (𝓝[>] (lam / M.μ)) atTop)
    (hreg : ∃ κ : ℝ, 0 < κ ∧ ∃ γ : ℝ, 0 < γ ∧
      Tendsto (fun lam => Flam F M.μ lam κ / Glam M lam κ) atTop (𝓝 γ))
    (y : ℝ → ℝ)
    (hy : ∀ lam : ℝ, 0 < lam → 0 < y lam ∧
      ∀ y' : ℝ, 0 < y' →
        surrogate (Flam F M.μ lam) delayFn (Glam M lam) (y lam) ≤
          surrogate (Flam F M.μ lam) delayFn (Glam M lam) y')
    (Nstar : ℝ → ℕ)
    (hN : ∀ lam : ℝ, 0 < lam → lam / M.μ < Nstar lam ∧
      ∀ N : ℕ, lam / M.μ < N → cost M F (Nstar lam) lam ≤ cost M F N lam) :
    Tendsto (fun lam => (staffCost M F lam (y lam) - F (lam / M.μ)) /
      (cost M F (Nstar lam) lam - F (lam / M.μ))) atTop (𝓝 1) := by sorry

end DimCallCenters.Rationalized
