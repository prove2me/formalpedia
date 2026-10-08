-- Prove2me | Theorems.Thm_DimCallCenters_EfficiencyDriven_lemma_3_2
-- name    : DimCallCenters.EfficiencyDriven.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T20:03:07.350869+00:00
-- url     : https://prove2.me/theorems/f394d6cc-e468-4730-9c69-300bb7db38e9
-- title:
--   Lemma 3.2 — rounding preserves asymptotic cost
-- statement:
--   Let $x^*_\lambda$ minimize the exact continuous cost and $N^*_\lambda$ minimize the cost over stable integer staffing levels. If a positive offset $z_\lambda$ has asymptotically the same exact continuous cost as $x^*_\lambda$, then rounding it preserves asymptotic optimality above the baseline staffing cost:
--
--   $$
--   \frac{C_\lambda(z_\lambda)}{C_\lambda(x^*_\lambda)}\to1
--   \quad\Longrightarrow\quad
--   \frac{S_\lambda(z_\lambda)-F(\lambda/\mu)}{C(N^*_\lambda,\lambda)-F(\lambda/\mu)}\to1.
--   $$
--
--   This connects the report's real-variable approximation to a feasible integer decision.
--
--   **Formalization Note** The theorem permits any positive $z_\lambda$. Every such function is the minimizer of some surrogate in equation (9), and the lemma's proof uses no additional property of that surrogate.
-- source:
--   Borst, Mandelbaum & Reiman, Dimensioning Large Call Centers, CWI Report PNA-R0015 (2000), p. 13, Lemma 3.2

import Mathlib
import Definitions.Def_DimCallCenters_EfficiencyDriven_Optima
import Definitions.Def_DimCallCenters_Rationalized_cost
import Definitions.Def_DimCallCenters_Rationalized_Clam
import Definitions.Def_DimCallCenters_Rationalized_staffCost

open Filter

namespace DimCallCenters.EfficiencyDriven

/-- Lemma 3.2, p. 13. The point z may be the minimizer of any surrogate. -/
theorem lemma_3_2 (M : DimCallCenters.Rationalized.WaitModel) (F : ℝ → ℝ)
    (Nstar : ℝ → ℕ) (x z : ℝ → ℝ)
    (hFconv : ConvexOn ℝ (Set.Ioi 0) F)
    (hFmono : StrictMonoOn F (Set.Ioi 0))
    (hN : IsDiscreteOpt M F Nstar)
    (hx : IsContinuousOpt M F x)
    (hz : ∀ lam, 0 < lam → 0 < z lam)
    (happrox : Tendsto (fun lam =>
      DimCallCenters.Rationalized.Clam M F lam (z lam) / DimCallCenters.Rationalized.Clam M F lam (x lam)) atTop (nhds 1)) :
    Tendsto (fun lam =>
      (DimCallCenters.Rationalized.staffCost M F lam (z lam) - F (lam / M.μ)) /
        (DimCallCenters.Rationalized.cost M F (Nstar lam) lam - F (lam / M.μ))) atTop (nhds 1) := by sorry

end DimCallCenters.EfficiencyDriven
