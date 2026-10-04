-- Prove2me | Theorems.Thm_DimCallCenters_Rationalized_lemma_3_2
-- name    : DimCallCenters.Rationalized.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T10:35:39.723498+00:00
-- url     : https://prove2.me/theorems/efc13892-1ab5-4be2-af6c-20c58d4c78eb
-- title:
--   Lemma 3.2 — rounding an asymptotically optimal continuous level
-- statement:
--   Assume the standing assumptions of Section 2 and let $F$ be convex and strictly increasing on $(0,\infty)$. For each $\lambda > 0$ let $x^*_\lambda > 0$ minimize $C_\lambda$ over $(0,\infty)$ (8), let $N^*_\lambda > \lambda/\mu$ be an integer minimizing $C(N,\lambda)$ over the integers $N > \lambda/\mu$ (7), and let $z_\lambda > 0$. If $C_\lambda(z_\lambda)/C_\lambda(x^*_\lambda) \to 1$ as $\lambda\to\infty$, then
--
--   $$\frac{S_\lambda(z_\lambda) - F(\lambda/\mu)}{C(N^*_\lambda,\lambda) - F(\lambda/\mu)} \to 1 \qquad (\lambda\to\infty).$$
--
--   So rounding a nearly optimal continuous staffing level to the cheaper neighbouring integer is nearly optimal for the discrete problem.
--
--   **Formalization Note** The paper states the lemma for the minimizer $z^*_\lambda$ of a surrogate (9); its proof uses only $z^*_\lambda > 0$, so it is stated for an arbitrary positive staffing function. This is equivalent, since every positive function is the minimizer of some surrogate. $S_\lambda$ omits the floor term when the floor is not a stable level (see the definition).
-- source:
--   Borst, Mandelbaum & Reiman, Dimensioning Large Call Centers, CWI Report PNA-R0015 (2000), p. 13, Lemma 3.2

import Mathlib
import Definitions.Def_DimCallCenters_Rationalized_Clam
import Definitions.Def_DimCallCenters_Rationalized_staffCost

open Filter Topology

namespace DimCallCenters.Rationalized

/-- Lemma 3.2 (p. 13). `x lam` is a minimizer `x*_λ` of `C_λ` over `(0, ∞)` (8), `Nstar lam` a
minimizer `N*_λ` of `C(·, λ)` over the integers `N > λ/μ` (7), and `z lam > 0` is any staffing
function. If `C_λ(z_λ) ≈ C_λ(x*_λ)`, then `S_λ(z_λ) - F(λ/μ) ≈ C(N*_λ, λ) - F(λ/μ)`. -/
theorem lemma_3_2 (M : WaitModel) (F : ℝ → ℝ)
    (hFconv : ConvexOn ℝ (Set.Ioi 0) F) (hFmono : StrictMonoOn F (Set.Ioi 0))
    (x z : ℝ → ℝ)
    (hx : ∀ lam : ℝ, 0 < lam → 0 < x lam ∧
      ∀ x' : ℝ, 0 < x' → Clam M F lam (x lam) ≤ Clam M F lam x')
    (hz : ∀ lam : ℝ, 0 < lam → 0 < z lam)
    (Nstar : ℝ → ℕ)
    (hN : ∀ lam : ℝ, 0 < lam → lam / M.μ < Nstar lam ∧
      ∀ N : ℕ, lam / M.μ < N → cost M F (Nstar lam) lam ≤ cost M F N lam)
    (hzx : Tendsto (fun lam => Clam M F lam (z lam) / Clam M F lam (x lam)) atTop (𝓝 1)) :
    Tendsto (fun lam => (staffCost M F lam (z lam) - F (lam / M.μ)) /
      (cost M F (Nstar lam) lam - F (lam / M.μ))) atTop (𝓝 1) := by sorry

end DimCallCenters.Rationalized
