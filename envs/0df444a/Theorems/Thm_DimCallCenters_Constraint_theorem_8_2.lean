-- Prove2me | Theorems.Thm_DimCallCenters_Constraint_theorem_8_2
-- name    : DimCallCenters.Constraint.theorem_8_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T02:01:33.742054+00:00
-- url     : https://prove2.me/theorems/1e717be1-c0b0-481f-809a-7f7766cede26
-- title:
--   Theorem 8.2 — the staffing rule P(y)G_λ(y) = M_λ is asymptotically optimal under a waiting-cost constraint
-- statement:
--   Let $(\mu, D)$ be a wait model, and let $M_\lambda > 0$ be a target for the waiting cost for every arrival rate $\lambda > 0$. Let $N^*_\lambda$ be the fewest servers meeting the target,
--
--   $$N^*_\lambda = \min\{N > \lambda/\mu \text{ integer} : K(N,\lambda) \le M_\lambda\}, \qquad K(N,\lambda) = \lambda\,\pi(N,\lambda/\mu)\,G(N,\lambda).$$
--
--   Suppose the **rationalized regime** (33): for some $\kappa > 0$ and some $\gamma \in (0,\infty)$,
--
--   $$\lim_{\lambda\to\infty}\frac{G_\lambda(\kappa)}{M_\lambda} = \gamma .$$
--
--   For each $\lambda > 0$ let $y^*_\lambda > 0$ solve $P(y)\,G_\lambda(y) = M_\lambda$, with $P$ the Halfin–Whitt delay function. Then
--
--   $$\lim_{\lambda\to\infty}\frac{T_\lambda(y^*_\lambda)}{M_\lambda} = 0,$$
--
--   where $T_\lambda$ is the rounding gap (32). That is, staffing $\lceil\lambda/\mu + y^*_\lambda\sqrt{\lambda/\mu}\rceil$ or $\lfloor\lambda/\mu + y^*_\lambda\sqrt{\lambda/\mu}\rfloor$ servers meets the waiting-cost constraint up to a relative error that vanishes as $\lambda \to \infty$, or matches the waiting cost of the optimal level up to the same error.
--
--   This is the square-root staffing rule for a waiting-cost constraint: the excess staffing $y^*_\lambda$ solves an equation in the Halfin–Whitt function instead of the Erlang-C formula.
--
--   **Formalization Note** $N^*_\lambda$ is a function of $\lambda$ given with its two defining properties, and $y^*_\lambda$ is any positive solution of the equation; existence and uniqueness are not assumed. In $T_\lambda$ the round-down term is omitted when $\lfloor N_\lambda(y^*_\lambda)\rfloor \le \lambda/\mu$, which can only make $T_\lambda$ larger. The paper's remark that $\limsup G_\lambda(\kappa)/M_\lambda < \infty$ would suffice is not used: the hypothesis is (33) as stated.
-- source:
--   Borst, Mandelbaum & Reiman, Dimensioning Large Call Centers, CWI Report PNA-R0015 (2000), pp. 25-26, Section 8.1, Eq. (33) and Theorem 8.2 (with Lemma 8.1, p. 24, and (31), (32))

import Mathlib
import Definitions.Def_DimCallCenters_Rationalized_delayFn
import Definitions.Def_DimCallCenters_Rationalized_Glam
import Definitions.Def_DimCallCenters_Constraint_gapCost

open Filter Topology

namespace DimCallCenters.Constraint

/-- Theorem 8.2 (rationalized regime under a waiting-cost constraint), pp. 25–26. Suppose that
for some `κ > 0`, `G_λ(κ) / M_λ → γ ∈ (0, ∞)` ((33)). Let `y*_λ > 0` solve
`P(y) G_λ(y) = M_λ`, and let `N*_λ` be the least integer `N > λ/μ` with `K(N, λ) ≤ M_λ` ((31)).
Then `T_λ(y*_λ) / M_λ → 0` as `λ → ∞`, with `T_λ` the rounding gap (32). -/
theorem theorem_8_2 (M : DimCallCenters.Rationalized.WaitModel) (Mlam : ℝ → ℝ) (hM : ∀ lam : ℝ, 0 < lam → 0 < Mlam lam)
    (hreg : ∃ κ : ℝ, 0 < κ ∧ ∃ γ : ℝ, 0 < γ ∧
      Tendsto (fun lam => DimCallCenters.Rationalized.Glam M lam κ / Mlam lam) atTop (𝓝 γ))
    (y : ℝ → ℝ)
    (hy : ∀ lam : ℝ, 0 < lam → 0 < y lam ∧ DimCallCenters.Rationalized.delayFn (y lam) * DimCallCenters.Rationalized.Glam M lam (y lam) = Mlam lam)
    (Nstar : ℝ → ℕ)
    (hNfeas : ∀ lam : ℝ, 0 < lam →
      lam / M.μ < (Nstar lam : ℝ) ∧ waitingCost M (Nstar lam) lam ≤ Mlam lam)
    (hNmin : ∀ lam : ℝ, 0 < lam → ∀ N : ℕ, lam / M.μ < (N : ℝ) →
      waitingCost M N lam ≤ Mlam lam → Nstar lam ≤ N) :
    Tendsto (fun lam => gapCost M lam (Nstar lam) (Mlam lam) (y lam) / Mlam lam)
      atTop (𝓝 0) := by sorry

end DimCallCenters.Constraint
