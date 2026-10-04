-- Prove2me | Theorems.Thm_DimCallCenters_Rationalized_corollary_3_3
-- name    : DimCallCenters.Rationalized.corollary_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T10:35:48.763213+00:00
-- url     : https://prove2.me/theorems/9a3b33e2-54fa-4b0e-b765-43eee8696bce
-- title:
--   Corollary 3.3 (Asymptotic Optimality) — the approximation principle
-- statement:
--   Assume the standing assumptions of Section 2 and let $F$ be convex and strictly increasing on $(0,\infty)$. For each $\lambda>0$ let $\hat F_\lambda,\hat\pi_\lambda,\hat G_\lambda$ be real functions, $\hat C_\lambda(z) = C[z;\hat F_\lambda,\hat\pi_\lambda,\hat G_\lambda]$, let $x^*_\lambda > 0$ minimize $C_\lambda$ (8), $z^*_\lambda > 0$ minimize $\hat C_\lambda$ (9) over $(0,\infty)$, and $N^*_\lambda$ be an optimal integer staffing level (7). If $C_\lambda(x^*_\lambda)/\hat C_\lambda(x^*_\lambda) \to 1$ and $C_\lambda(z^*_\lambda)/\hat C_\lambda(z^*_\lambda) \to 1$, then the staffing function $z^*_\lambda$ is **asymptotically optimal**:
--
--   $$\frac{S_\lambda(z^*_\lambda) - F(\lambda/\mu)}{C(N^*_\lambda,\lambda) - F(\lambda/\mu)} \to 1 \qquad (\lambda\to\infty).$$
--
--   Every regime theorem of the paper (5.1, 6.1, 7.1) is obtained by checking the two hypotheses for a specific surrogate.
--
--   **Formalization Note** Argmins are hypotheses (any minimizer); $\lambda\to\infty$ is over the reals.
-- source:
--   Borst, Mandelbaum & Reiman, Dimensioning Large Call Centers, CWI Report PNA-R0015 (2000), p. 14, Corollary 3.3 (Asymptotic Optimality)

import Mathlib
import Definitions.Def_DimCallCenters_Rationalized_Clam
import Definitions.Def_DimCallCenters_Rationalized_surrogate
import Definitions.Def_DimCallCenters_Rationalized_staffCost

open Filter Topology

namespace DimCallCenters.Rationalized

/-- Corollary 3.3 (Asymptotic Optimality), p. 14. With `x*_λ` a minimizer of `C_λ` (8), `z*_λ`
a minimizer of the surrogate `Ĉ_λ = C[·; F̂_λ, π̂_λ, Ĝ_λ]` (9) and `N*_λ` an optimal integer
staffing level (7): if `C_λ(x*_λ) ≈ Ĉ_λ(x*_λ)` and `C_λ(z*_λ) ≈ Ĉ_λ(z*_λ)`, then
`S_λ(z*_λ) - F(λ/μ) ≈ C(N*_λ, λ) - F(λ/μ)` as `λ → ∞`. -/
theorem corollary_3_3 (M : WaitModel) (F : ℝ → ℝ)
    (hFconv : ConvexOn ℝ (Set.Ioi 0) F) (hFmono : StrictMonoOn F (Set.Ioi 0))
    (Fh pih Gh : ℝ → ℝ → ℝ) (x z : ℝ → ℝ)
    (hx : ∀ lam : ℝ, 0 < lam → 0 < x lam ∧
      ∀ x' : ℝ, 0 < x' → Clam M F lam (x lam) ≤ Clam M F lam x')
    (hz : ∀ lam : ℝ, 0 < lam → 0 < z lam ∧
      ∀ z' : ℝ, 0 < z' →
        surrogate (Fh lam) (pih lam) (Gh lam) (z lam) ≤ surrogate (Fh lam) (pih lam) (Gh lam) z')
    (Nstar : ℝ → ℕ)
    (hN : ∀ lam : ℝ, 0 < lam → lam / M.μ < Nstar lam ∧
      ∀ N : ℕ, lam / M.μ < N → cost M F (Nstar lam) lam ≤ cost M F N lam)
    (hxapprox : Tendsto (fun lam => Clam M F lam (x lam) /
      surrogate (Fh lam) (pih lam) (Gh lam) (x lam)) atTop (𝓝 1))
    (hzapprox : Tendsto (fun lam => Clam M F lam (z lam) /
      surrogate (Fh lam) (pih lam) (Gh lam) (z lam)) atTop (𝓝 1)) :
    Tendsto (fun lam => (staffCost M F lam (z lam) - F (lam / M.μ)) /
      (cost M F (Nstar lam) lam - F (lam / M.μ))) atTop (𝓝 1) := by sorry

end DimCallCenters.Rationalized
