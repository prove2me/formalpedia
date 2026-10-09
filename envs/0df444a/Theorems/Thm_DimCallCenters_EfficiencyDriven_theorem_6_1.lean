-- Prove2me | Theorems.Thm_DimCallCenters_EfficiencyDriven_theorem_6_1
-- name    : DimCallCenters.EfficiencyDriven.theorem_6_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T20:03:30.400225+00:00
-- url     : https://prove2.me/theorems/b058416f-e55a-4402-b5b0-faaf72cc3002
-- title:
--   Theorem 6.1 — efficiency-driven staffing is asymptotically optimal
-- statement:
--   Fix a positive service rate $\mu$, a convex strictly increasing staffing cost $F$, and a family of strictly increasing waiting penalties $D_\lambda$ with finite exponential expectations. Suppose that for every fixed $\kappa>0$ the staffing cost dominates the waiting cost in the exact sense of equation (23):
--
--   $$
--   \frac{F_\lambda(\kappa)}{G_\lambda(\kappa)}\longrightarrow+\infty.
--   $$
--
--   For each $\lambda>0$, let $N^*_\lambda$ minimize exact cost over stable integer staffing levels and let $y^*_\lambda>0$ minimize $F_\lambda(y)+G_\lambda(y)$ over positive real offsets. Then, with the report's integer rounding cost $S_\lambda$,
--
--   $$
--   \frac{S_\lambda(y^*_\lambda)-F(\lambda/\mu)}{C(N^*_\lambda,\lambda)-F(\lambda/\mu)}\longrightarrow1.
--   $$
--
--   Thus the simpler surrogate with delay probability replaced by one attains asymptotically optimal incremental total cost.
--
--   **Formalization Note** The report asserts divergence of $G(N,\lambda)$ as $N$ decreases to $\lambda/\mu$, but this requires an additional unboundedness condition on $D_\lambda$. The theorem states this divergence explicitly. An unstable floor is excluded from $S_\lambda$. No exact continuous optimum is assumed in the goal.
-- source:
--   Borst, Mandelbaum & Reiman, Dimensioning Large Call Centers, CWI Report PNA-R0015 (2000), p. 19, Theorem 6.1, Eq. (23)-(24); p. 14, Corollary 3.3

import Mathlib
import Definitions.Def_DimCallCenters_EfficiencyDriven_Optima
import Definitions.Def_DimCallCenters_Rationalized_waitCost
import Definitions.Def_DimCallCenters_Rationalized_cost
import Definitions.Def_DimCallCenters_Rationalized_Flam
import Definitions.Def_DimCallCenters_Rationalized_Glam
import Definitions.Def_DimCallCenters_Rationalized_staffCost

open Filter

namespace DimCallCenters.EfficiencyDriven

/-- Theorem 6.1, p. 19: asymptotic optimality in the efficiency-driven regime. -/
theorem theorem_6_1 (M : DimCallCenters.Rationalized.WaitModel) (F : ℝ → ℝ)
    (Nstar : ℝ → ℕ) (y : ℝ → ℝ)
    (hFconv : ConvexOn ℝ (Set.Ioi 0) F)
    (hFmono : StrictMonoOn F (Set.Ioi 0))
    (hGinf : ∀ lam, 0 < lam →
      Tendsto (fun N : ℝ => DimCallCenters.Rationalized.waitCost M N lam)
        (nhdsWithin (lam / M.μ) (Set.Ioi (lam / M.μ))) atTop)
    (hreg : ∀ κ, 0 < κ →
      Tendsto (fun lam => DimCallCenters.Rationalized.Flam F M.μ lam κ / DimCallCenters.Rationalized.Glam M lam κ)
        atTop atTop)
    (hN : IsDiscreteOpt M F Nstar)
    (hy : IsSurrogateOpt (fun lam => DimCallCenters.Rationalized.Flam F M.μ lam)
      (fun _ _ => 1) (fun lam => DimCallCenters.Rationalized.Glam M lam) y) :
    Tendsto (fun lam =>
      (DimCallCenters.Rationalized.staffCost M F lam (y lam) - F (lam / M.μ)) /
        (DimCallCenters.Rationalized.cost M F (Nstar lam) lam - F (lam / M.μ))) atTop (nhds 1) := by sorry

end DimCallCenters.EfficiencyDriven
