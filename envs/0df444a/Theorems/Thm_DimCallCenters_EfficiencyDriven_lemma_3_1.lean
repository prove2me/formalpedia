-- Prove2me | Theorems.Thm_DimCallCenters_EfficiencyDriven_lemma_3_1
-- name    : DimCallCenters.EfficiencyDriven.lemma_3_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T20:02:51.25887+00:00
-- url     : https://prove2.me/theorems/6ff9d752-5e60-49c7-b07e-455b34ec1406
-- title:
--   Lemma 3.1 — approximation at both minimizers
-- statement:
--   Let $x^*_\lambda$ minimize the exact continuous cost $C_\lambda$, and let $z^*_\lambda$ minimize a surrogate $\widehat C_\lambda$ over positive offsets. If the surrogate is asymptotically equivalent to the exact cost at both minimizers, then the exact costs at those minimizers are asymptotically equivalent:
--
--   $$
--   \frac{C_\lambda(x^*_\lambda)}{\widehat C_\lambda(x^*_\lambda)}\to1,
--   \quad\frac{C_\lambda(z^*_\lambda)}{\widehat C_\lambda(z^*_\lambda)}\to1
--   \quad\Longrightarrow\quad
--   \frac{C_\lambda(z^*_\lambda)}{C_\lambda(x^*_\lambda)}\to1.
--   $$
--
--   This is the report's comparison principle for a continuously optimized approximation.
-- source:
--   Borst, Mandelbaum & Reiman, Dimensioning Large Call Centers, CWI Report PNA-R0015 (2000), p. 13, Lemma 3.1

import Mathlib
import Definitions.Def_DimCallCenters_EfficiencyDriven_Optima
import Definitions.Def_DimCallCenters_Rationalized_Clam
import Definitions.Def_DimCallCenters_Rationalized_surrogate

open Filter

namespace DimCallCenters.EfficiencyDriven

/-- Lemma 3.1, p. 13. -/
theorem lemma_3_1 (M : DimCallCenters.Rationalized.WaitModel) (F : ℝ → ℝ)
    (Fh pih Gh : ℝ → ℝ → ℝ) (x z : ℝ → ℝ)
    (hFconv : ConvexOn ℝ (Set.Ioi 0) F)
    (hFmono : StrictMonoOn F (Set.Ioi 0))
    (hx : IsContinuousOpt M F x)
    (hz : IsSurrogateOpt Fh pih Gh z)
    (happroxX : Tendsto (fun lam =>
      DimCallCenters.Rationalized.Clam M F lam (x lam) /
        DimCallCenters.Rationalized.surrogate (Fh lam) (pih lam) (Gh lam) (x lam)) atTop (nhds 1))
    (happroxZ : Tendsto (fun lam =>
      DimCallCenters.Rationalized.Clam M F lam (z lam) /
        DimCallCenters.Rationalized.surrogate (Fh lam) (pih lam) (Gh lam) (z lam)) atTop (nhds 1)) :
    Tendsto (fun lam => DimCallCenters.Rationalized.Clam M F lam (z lam) / DimCallCenters.Rationalized.Clam M F lam (x lam))
      atTop (nhds 1) := by sorry

end DimCallCenters.EfficiencyDriven
