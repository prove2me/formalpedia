-- Prove2me | Theorems.Thm_DimCallCenters_Constraint_lemma_8_1
-- name    : DimCallCenters.Constraint.lemma_8_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T02:01:35.903983+00:00
-- url     : https://prove2.me/theorems/49b028e3-94b9-4e23-a2c3-4d3e436e7329
-- title:
--   Lemma 8.1 — asymptotic optimality of an approximate solution of the constraint equation
-- statement:
--   Let $(\mu, D)$ be a wait model and $M_\lambda > 0$ a waiting-cost target for every $\lambda > 0$. Let $N^*_\lambda$ be the least integer $N > \lambda/\mu$ with $K(N,\lambda) \le M_\lambda$, where $K(N,\lambda) = \lambda\pi(N,\lambda/\mu)G(N,\lambda)$ (problem (31)). Let $\hat\pi_\lambda(\cdot)$ and $\hat G_\lambda(\cdot)$ be arbitrary real functions and $z^*_\lambda > 0$ a solution of $\hat\pi_\lambda(z)\hat G_\lambda(z) = M_\lambda$, and write $\hat K_\lambda(y) = \hat\pi_\lambda(y)\hat G_\lambda(y)$. If
--
--   $$\lim_{\lambda\to\infty}\frac{K_\lambda(z^*_\lambda)}{\hat K_\lambda(z^*_\lambda)} = 1, \qquad K_\lambda(x) = \pi_\lambda(x)G_\lambda(x),$$
--
--   then
--
--   $$\lim_{\lambda\to\infty}\frac{T_\lambda(z^*_\lambda)}{M_\lambda} = 0,$$
--
--   where $T_\lambda$ is the rounding gap (32).
--
--   This is the paper's framework for the constraint problem: any staffing function obtained from an asymptotically exact approximation $\hat\pi_\lambda \hat G_\lambda$ of the continuous waiting cost meets the target up to a vanishing relative error after rounding. Theorems 8.2, 8.6 and 8.9 apply it with specific approximations.
--
--   **Formalization Note** $N^*_\lambda$ is a function of $\lambda$ given with its two defining properties (feasible, and below every feasible integer level), not computed. $z^*_\lambda$ is any positive solution; uniqueness is not assumed. In $T_\lambda$ the round-down term is omitted when $\lfloor N_\lambda(z)\rfloor \le \lambda/\mu$.
-- source:
--   Borst, Mandelbaum & Reiman, Dimensioning Large Call Centers, CWI Report PNA-R0015 (2000), p. 24, Lemma 8.1 (with (31), (32))

import Mathlib
import Definitions.Def_DimCallCenters_Constraint_Klam
import Definitions.Def_DimCallCenters_Constraint_gapCost

open Filter Topology

namespace DimCallCenters.Constraint

/-- Lemma 8.1 (Asymptotic Optimality), p. 24. Let `N*_λ` be the least integer `N > λ/μ` with
`K(N, λ) ≤ M_λ` ((31)), and let `z*_λ > 0` solve `π̂_λ(z) Ĝ_λ(z) = M_λ`. If
`K_λ(z*_λ) / (π̂_λ(z*_λ) Ĝ_λ(z*_λ)) → 1` as `λ → ∞`, then `T_λ(z*_λ) / M_λ → 0`, with `T_λ`
the rounding gap (32). -/
theorem lemma_8_1 (M : DimCallCenters.Rationalized.WaitModel) (Mlam : ℝ → ℝ) (hM : ∀ lam : ℝ, 0 < lam → 0 < Mlam lam)
    (Nstar : ℝ → ℕ)
    (hNfeas : ∀ lam : ℝ, 0 < lam →
      lam / M.μ < (Nstar lam : ℝ) ∧ waitingCost M (Nstar lam) lam ≤ Mlam lam)
    (hNmin : ∀ lam : ℝ, 0 < lam → ∀ N : ℕ, lam / M.μ < (N : ℝ) →
      waitingCost M N lam ≤ Mlam lam → Nstar lam ≤ N)
    (pih Gh : ℝ → ℝ → ℝ) (z : ℝ → ℝ)
    (hz : ∀ lam : ℝ, 0 < lam → 0 < z lam ∧ pih lam (z lam) * Gh lam (z lam) = Mlam lam)
    (happrox : Tendsto (fun lam => Klam M lam (z lam) / (pih lam (z lam) * Gh lam (z lam)))
      atTop (𝓝 1)) :
    Tendsto (fun lam => gapCost M lam (Nstar lam) (Mlam lam) (z lam) / Mlam lam)
      atTop (𝓝 0) := by sorry

end DimCallCenters.Constraint
