-- Prove2me | Theorems.Thm_DimCallCenters_QualityDriven_lemma_3_2
-- name    : DimCallCenters.QualityDriven.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T19:56:19.821835+00:00
-- url     : https://prove2.me/theorems/dc23905b-1174-40d9-bf69-ba82b771591a
-- title:
--   Lemma 3.2 — rounding an asymptotically optimal continuous level
-- statement:
--   Let $(\mu, D)$ be a waiting model and $F$ a staffing cost function, convex and strictly increasing on $(0,\infty)$. For every $\lambda > 0$ let $x^*_\lambda > 0$ minimize $C_\lambda$ over $(0,\infty)$, let $N^*_\lambda$ be an optimal staffing level, i.e. an integer $N^*_\lambda > \lambda/\mu$ minimizing $C(\cdot,\lambda)$ over the integers $N > \lambda/\mu$, and let $z_\lambda > 0$ be any staffing function. If $C_\lambda(z_\lambda)/C_\lambda(x^*_\lambda) \to 1$ as $\lambda\to\infty$, then
--
--   $$
--   \lim_{\lambda\to\infty}\frac{S_\lambda(z_\lambda) - F(\lambda/\mu)}{C(N^*_\lambda,\lambda) - F(\lambda/\mu)} = 1 ,
--   $$
--
--   with $S_\lambda$ the rounded cost of display (10).
--
--   The lemma turns asymptotic optimality of a continuous staffing level into asymptotic optimality of its integer rounding.
--
--   **Formalization Note** The paper states the lemma for the minimizer $z^*_\lambda$ of (9); its proof never uses how $z^*_\lambda$ is obtained, and every positive function is the minimizer (9) of some surrogate, so the statement for an arbitrary positive $z_\lambda$ is equivalent. In $S_\lambda$ the floor term is omitted when it is not a stable staffing level.
-- source:
--   Borst, Mandelbaum & Reiman, Dimensioning Large Call Centers, CWI Report PNA-R0015 (2000), p. 13, Lemma 3.2

import Mathlib
import Definitions.Def_DimCallCenters_Rationalized_Clam
import Definitions.Def_DimCallCenters_Rationalized_staffCost

open Filter Topology

namespace DimCallCenters.QualityDriven

/-- Lemma 3.2 (p. 13). `x lam` is a minimizer `x*_λ` of `C_λ` over `(0, ∞)` (8), `Nstar lam` a
minimizer `N*_λ` of `C(·, λ)` over the integers `N > λ/μ` (7), and `z lam > 0` is any staffing
function. If `C_λ(z_λ) ≈ C_λ(x*_λ)`, then `S_λ(z_λ) - F(λ/μ) ≈ C(N*_λ, λ) - F(λ/μ)`. -/
theorem lemma_3_2 (M : DimCallCenters.Rationalized.WaitModel) (F : ℝ → ℝ)
    (hFconv : ConvexOn ℝ (Set.Ioi 0) F) (hFmono : StrictMonoOn F (Set.Ioi 0))
    (x z : ℝ → ℝ)
    (hx : ∀ lam : ℝ, 0 < lam → 0 < x lam ∧
      ∀ x' : ℝ, 0 < x' → DimCallCenters.Rationalized.Clam M F lam (x lam) ≤ DimCallCenters.Rationalized.Clam M F lam x')
    (hz : ∀ lam : ℝ, 0 < lam → 0 < z lam)
    (Nstar : ℝ → ℕ)
    (hN : ∀ lam : ℝ, 0 < lam → lam / M.μ < Nstar lam ∧
      ∀ N : ℕ, lam / M.μ < N → DimCallCenters.Rationalized.cost M F (Nstar lam) lam ≤ DimCallCenters.Rationalized.cost M F N lam)
    (hzx : Tendsto (fun lam => DimCallCenters.Rationalized.Clam M F lam (z lam) / DimCallCenters.Rationalized.Clam M F lam (x lam)) atTop (𝓝 1)) :
    Tendsto (fun lam => (DimCallCenters.Rationalized.staffCost M F lam (z lam) - F (lam / M.μ)) /
      (DimCallCenters.Rationalized.cost M F (Nstar lam) lam - F (lam / M.μ))) atTop (𝓝 1) := by sorry

end DimCallCenters.QualityDriven
