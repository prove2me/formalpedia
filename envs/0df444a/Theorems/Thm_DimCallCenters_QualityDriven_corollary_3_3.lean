-- Prove2me | Theorems.Thm_DimCallCenters_QualityDriven_corollary_3_3
-- name    : DimCallCenters.QualityDriven.corollary_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T19:56:29.935987+00:00
-- url     : https://prove2.me/theorems/a280cb86-59b6-413c-a6e8-188ff0ece97f
-- title:
--   Corollary 3.3 — asymptotic optimality criterion
-- statement:
--   Let $(\mu, D)$ be a waiting model and $F$ a staffing cost function, convex and strictly increasing on $(0,\infty)$. For every $\lambda > 0$ let $\hat F_\lambda,\hat\pi_\lambda,\hat G_\lambda$ be real functions with $\hat C_\lambda(z) = C[z;\hat F_\lambda,\hat\pi_\lambda,\hat G_\lambda]$, and let
--
--   1. $x^*_\lambda > 0$ minimize $C_\lambda$ over $(0,\infty)$, display (8);
--   2. $z^*_\lambda > 0$ minimize $\hat C_\lambda$ over $(0,\infty)$, display (9);
--   3. $N^*_\lambda$ be an integer $> \lambda/\mu$ minimizing $C(\cdot,\lambda)$ over the integers $N > \lambda/\mu$, display (7).
--
--   If $C_\lambda(x^*_\lambda)/\hat C_\lambda(x^*_\lambda) \to 1$ and $C_\lambda(z^*_\lambda)/\hat C_\lambda(z^*_\lambda) \to 1$ as $\lambda\to\infty$, then the staffing function $z^*_\lambda$ is asymptotically optimal:
--
--   $$
--   \lim_{\lambda\to\infty}\frac{S_\lambda(z^*_\lambda) - F(\lambda/\mu)}{C(N^*_\lambda,\lambda) - F(\lambda/\mu)} = 1 .
--   $$
--
--   This is the criterion that every regime theorem of the paper invokes: it reduces asymptotic optimality to asymptotic exactness of the surrogate cost at two points.
--
--   **Formalization Note** In $S_\lambda$ the floor term is omitted when it is not a stable staffing level. Minimizers are function arguments with minimality hypotheses at every $\lambda > 0$.
-- source:
--   Borst, Mandelbaum & Reiman, Dimensioning Large Call Centers, CWI Report PNA-R0015 (2000), p. 14, Corollary 3.3

import Mathlib
import Definitions.Def_DimCallCenters_Rationalized_Clam
import Definitions.Def_DimCallCenters_Rationalized_surrogate
import Definitions.Def_DimCallCenters_Rationalized_staffCost

open Filter Topology

namespace DimCallCenters.QualityDriven

/-- Corollary 3.3 (Asymptotic Optimality), p. 14. With `x*_λ` a minimizer of `C_λ` (8), `z*_λ`
a minimizer of the DimCallCenters.Rationalized.surrogate `Ĉ_λ = C[·; F̂_λ, π̂_λ, Ĝ_λ]` (9) and `N*_λ` an optimal integer
staffing level (7): if `C_λ(x*_λ) ≈ Ĉ_λ(x*_λ)` and `C_λ(z*_λ) ≈ Ĉ_λ(z*_λ)`, then
`S_λ(z*_λ) - F(λ/μ) ≈ C(N*_λ, λ) - F(λ/μ)` as `λ → ∞`. -/
theorem corollary_3_3 (M : DimCallCenters.Rationalized.WaitModel) (F : ℝ → ℝ)
    (hFconv : ConvexOn ℝ (Set.Ioi 0) F) (hFmono : StrictMonoOn F (Set.Ioi 0))
    (Fh pih Gh : ℝ → ℝ → ℝ) (x z : ℝ → ℝ)
    (hx : ∀ lam : ℝ, 0 < lam → 0 < x lam ∧
      ∀ x' : ℝ, 0 < x' → DimCallCenters.Rationalized.Clam M F lam (x lam) ≤ DimCallCenters.Rationalized.Clam M F lam x')
    (hz : ∀ lam : ℝ, 0 < lam → 0 < z lam ∧
      ∀ z' : ℝ, 0 < z' →
        DimCallCenters.Rationalized.surrogate (Fh lam) (pih lam) (Gh lam) (z lam) ≤ DimCallCenters.Rationalized.surrogate (Fh lam) (pih lam) (Gh lam) z')
    (Nstar : ℝ → ℕ)
    (hN : ∀ lam : ℝ, 0 < lam → lam / M.μ < Nstar lam ∧
      ∀ N : ℕ, lam / M.μ < N → DimCallCenters.Rationalized.cost M F (Nstar lam) lam ≤ DimCallCenters.Rationalized.cost M F N lam)
    (hxapprox : Tendsto (fun lam => DimCallCenters.Rationalized.Clam M F lam (x lam) /
      DimCallCenters.Rationalized.surrogate (Fh lam) (pih lam) (Gh lam) (x lam)) atTop (𝓝 1))
    (hzapprox : Tendsto (fun lam => DimCallCenters.Rationalized.Clam M F lam (z lam) /
      DimCallCenters.Rationalized.surrogate (Fh lam) (pih lam) (Gh lam) (z lam)) atTop (𝓝 1)) :
    Tendsto (fun lam => (DimCallCenters.Rationalized.staffCost M F lam (z lam) - F (lam / M.μ)) /
      (DimCallCenters.Rationalized.cost M F (Nstar lam) lam - F (lam / M.μ))) atTop (𝓝 1) := by sorry

end DimCallCenters.QualityDriven
