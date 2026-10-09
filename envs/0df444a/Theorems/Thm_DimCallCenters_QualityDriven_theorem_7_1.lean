-- Prove2me | Theorems.Thm_DimCallCenters_QualityDriven_theorem_7_1
-- name    : DimCallCenters.QualityDriven.theorem_7_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T01:35:19.714248+00:00
-- url     : https://prove2.me/theorems/8b610958-e26f-464c-a4ea-dec2ec7605c9
-- title:
--   Theorem 7.1 — asymptotically optimal staffing in the quality-driven regime
-- statement:
--   Let $(\mu, D)$ be a waiting model and let $F$ be a staffing cost function that is convex and strictly increasing on $(0,\infty)$. Assume that
--
--   1. for every $\lambda > 0$, $G(N,\lambda) \to \infty$ as $N \downarrow \lambda/\mu$;
--   2. the regime is **quality-driven**, display (27): for every $\kappa > 0$, $F_\lambda(\kappa) \stackrel{\infty}{\ll} G_\lambda(\kappa)$, i.e.
--   $$
--   \lim_{\lambda\to\infty}\frac{F_\lambda(\kappa)}{G_\lambda(\kappa)} = 0 ;
--   $$
--   3. for every $\lambda > 0$, $y^*_\lambda > 0$ minimizes $C[y;F_\lambda,Q_\lambda,G_\lambda] = F_\lambda(y) + Q_\lambda(y)\,G_\lambda(y)$ over $y > 0$;
--   4. for every $\lambda > 0$, $N^*_\lambda$ is an integer $> \lambda/\mu$ minimizing the total cost $C(\cdot,\lambda)$ over the integers $N > \lambda/\mu$.
--
--   Then the staffing function $y^*_\lambda$ is asymptotically optimal in the sense of Corollary 3.3:
--
--   $$
--   \lim_{\lambda\to\infty}\frac{S_\lambda(y^*_\lambda) - F(\lambda/\mu)}{C(N^*_\lambda,\lambda) - F(\lambda/\mu)} = 1 ,
--   $$
--
--   where $S_\lambda(y) = \min\{C(\lfloor N_\lambda(y)\rfloor,\lambda), C(\lceil N_\lambda(y)\rceil,\lambda)\}$ is the cost of rounding $N_\lambda(y) = \lambda/\mu + y\sqrt{\lambda/\mu}$ to the cheaper neighbouring integer.
--
--   When waiting is expensive compared with staffing, the optimal number of servers exceeds the offered load by more than any fixed multiple of its square root, and the Halfin–Whitt delay function no longer describes the delay probability; the theorem says that replacing the delay probability by its Stirling-type approximation $Q_\lambda$ still gives an asymptotically optimal staffing rule.
--
--   **Formalization Note** Assumption 1 is added. The paper asserts it on p. 12 to show that the continuous optimum $x^*_\lambda$ exists, but it does not follow from the standing assumptions (it holds exactly when $D_\lambda$ is unbounded). In $S_\lambda$ the floor term is omitted when it is not a stable staffing level. $\lambda \to \infty$ is the `atTop` filter on the positive reals; minimizers are function arguments, and the theorem holds for every choice among ties.
-- source:
--   Borst, Mandelbaum & Reiman, Dimensioning Large Call Centers, CWI Report PNA-R0015 (2000), p. 21, Theorem 7.1 (with Section 7 preamble, Eq. (27))

import Mathlib
import Definitions.Def_DimCallCenters_Rationalized_Flam
import Definitions.Def_DimCallCenters_Rationalized_Glam
import Definitions.Def_DimCallCenters_Rationalized_surrogate
import Definitions.Def_DimCallCenters_QualityDriven_Qlam
import Definitions.Def_DimCallCenters_Rationalized_staffCost

open Filter Topology

namespace DimCallCenters.QualityDriven

/-- Theorem 7.1 (p. 21). In the quality-driven regime (27) — `F_λ(κ) / G_λ(κ) → 0` for every
`κ > 0` — the staffing function `y*_λ = argmin_{y>0} C[y; F_λ, Q_λ, G_λ]
= argmin_{y>0} F_λ(y) + Q_λ(y) G_λ(y)` is asymptotically optimal in the sense of Corollary 3.3:
`S_λ(y*_λ) - F(λ/μ) ≈ C(N*_λ, λ) - F(λ/μ)` as `λ → ∞`. The hypothesis `hGinf`
(`G(N, λ) → ∞` as `N ↓ λ/μ`) is asserted on p. 12 of the paper but does not follow from its
standing assumptions; it is added here. -/
theorem theorem_7_1 (M : DimCallCenters.Rationalized.WaitModel) (F : ℝ → ℝ)
    (hFconv : ConvexOn ℝ (Set.Ioi 0) F) (hFmono : StrictMonoOn F (Set.Ioi 0))
    (hGinf : ∀ lam : ℝ, 0 < lam →
      Tendsto (fun N => DimCallCenters.Rationalized.waitCost M N lam) (𝓝[>] (lam / M.μ)) atTop)
    (hreg : ∀ κ : ℝ, 0 < κ →
      Tendsto (fun lam => DimCallCenters.Rationalized.Flam F M.μ lam κ / DimCallCenters.Rationalized.Glam M lam κ) atTop (𝓝 0))
    (y : ℝ → ℝ)
    (hy : ∀ lam : ℝ, 0 < lam → 0 < y lam ∧
      ∀ y' : ℝ, 0 < y' →
        DimCallCenters.Rationalized.surrogate (DimCallCenters.Rationalized.Flam F M.μ lam) (Qlam M.μ lam) (DimCallCenters.Rationalized.Glam M lam) (y lam) ≤
          DimCallCenters.Rationalized.surrogate (DimCallCenters.Rationalized.Flam F M.μ lam) (Qlam M.μ lam) (DimCallCenters.Rationalized.Glam M lam) y')
    (Nstar : ℝ → ℕ)
    (hN : ∀ lam : ℝ, 0 < lam → lam / M.μ < Nstar lam ∧
      ∀ N : ℕ, lam / M.μ < N → DimCallCenters.Rationalized.cost M F (Nstar lam) lam ≤ DimCallCenters.Rationalized.cost M F N lam) :
    Tendsto (fun lam => (DimCallCenters.Rationalized.staffCost M F lam (y lam) - F (lam / M.μ)) /
      (DimCallCenters.Rationalized.cost M F (Nstar lam) lam - F (lam / M.μ))) atTop (𝓝 1) := by sorry

end DimCallCenters.QualityDriven
