-- Prove2me | Theorems.Thm_DimCallCenters_EfficiencyDriven_corollary_3_3
-- name    : DimCallCenters.EfficiencyDriven.corollary_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T20:03:22.171692+00:00
-- url     : https://prove2.me/theorems/0b1c558a-7f08-4b32-bda1-3e43a5c6b686
-- title:
--   Corollary 3.3 — asymptotic optimality principle
-- statement:
--   Let $x^*_\lambda$ and $z^*_\lambda$ minimize the exact and surrogate continuous objectives, respectively, and let $N^*_\lambda$ minimize the stable integer cost. Suppose the surrogate is asymptotically equivalent to the exact objective at both continuous minimizers. Then
--
--   $$
--   \frac{S_\lambda(z^*_\lambda)-F(\lambda/\mu)}{C(N^*_\lambda,\lambda)-F(\lambda/\mu)}\longrightarrow1.
--   $$
--
--   This is the report's general criterion for converting a continuous surrogate optimum into an asymptotically optimal integer staffing rule.
-- source:
--   Borst, Mandelbaum & Reiman, Dimensioning Large Call Centers, CWI Report PNA-R0015 (2000), p. 14, Corollary 3.3

import Mathlib
import Definitions.Def_DimCallCenters_EfficiencyDriven_Optima
import Definitions.Def_DimCallCenters_Rationalized_cost
import Definitions.Def_DimCallCenters_Rationalized_Clam
import Definitions.Def_DimCallCenters_Rationalized_surrogate
import Definitions.Def_DimCallCenters_Rationalized_staffCost

open Filter

namespace DimCallCenters.EfficiencyDriven

/-- Corollary 3.3 (Asymptotic Optimality), p. 14. -/
theorem corollary_3_3 (M : DimCallCenters.Rationalized.WaitModel) (F : ℝ → ℝ)
    (Fh pih Gh : ℝ → ℝ → ℝ) (Nstar : ℝ → ℕ) (x z : ℝ → ℝ)
    (hFconv : ConvexOn ℝ (Set.Ioi 0) F)
    (hFmono : StrictMonoOn F (Set.Ioi 0))
    (hN : IsDiscreteOpt M F Nstar)
    (hx : IsContinuousOpt M F x)
    (hz : IsSurrogateOpt Fh pih Gh z)
    (happroxX : Tendsto (fun lam =>
      DimCallCenters.Rationalized.Clam M F lam (x lam) /
        DimCallCenters.Rationalized.surrogate (Fh lam) (pih lam) (Gh lam) (x lam)) atTop (nhds 1))
    (happroxZ : Tendsto (fun lam =>
      DimCallCenters.Rationalized.Clam M F lam (z lam) /
        DimCallCenters.Rationalized.surrogate (Fh lam) (pih lam) (Gh lam) (z lam)) atTop (nhds 1)) :
    Tendsto (fun lam =>
      (DimCallCenters.Rationalized.staffCost M F lam (z lam) - F (lam / M.μ)) /
        (DimCallCenters.Rationalized.cost M F (Nstar lam) lam - F (lam / M.μ))) atTop (nhds 1) := by sorry

end DimCallCenters.EfficiencyDriven
