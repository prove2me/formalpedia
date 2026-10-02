-- Prove2me | Theorems.Thm_DualSSD_MeanRisk_meanGini_ssd_consistent
-- name    : DualSSD.MeanRisk.meanGini_ssd_consistent
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T00:07:48.622011+00:00
-- url     : https://prove2.me/theorems/7ed332a6-0514-4888-af64-ad8844f81ec9
-- title:
--   Proposition 4.5 — the mean–Gini model is consistent with SSD, strictly for strict dominance
-- statement:
--   For integrable random variables $X$ and $Y$ the following implications hold:
--
--   $$X\succeq_{SSD}Y\ \Longrightarrow\ \mu_X-\Gamma_X\ge\mu_Y-\Gamma_Y,\qquad X\succ_{SSD}Y\ \Longrightarrow\ \mu_X-\Gamma_X>\mu_Y-\Gamma_Y.$$
--
--   Here $\Gamma$ is the Gini mean difference (3.8). The strict form is what makes optimal solutions of mean–Gini models SSD-efficient.
-- source:
--   Ogryczak, Ruszczyński, Dual Stochastic Dominance and Related Mean-Risk Models, SIAM J. Optim. 13 (2002), pp. 71–72, Proposition 4.5, eqs. (4.6)–(4.7)

import Mathlib
import Definitions.Def_DualSSD_MeanRisk_gini
import Definitions.Def_DualSSD_MeanRisk_ssdEfficient

namespace DualSSD.MeanRisk

open MeasureTheory

/-- **Proposition 4.5** (Ogryczak–Ruszczyński 2002, pp. 71–72). For integrable random variables
`X` and `Y`:
(4.6) `X ⪰_SSD Y ⇒ μ_X − Γ_X ≥ μ_Y − Γ_Y`, and
(4.7) `X ≻_SSD Y ⇒ μ_X − Γ_X > μ_Y − Γ_Y`. -/
theorem meanGini_ssd_consistent {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X Y : Ω → ℝ) (hX : Integrable X P) (hY : Integrable Y P) :
    (Shared.SSD P X Y → mean P Y - gini P Y ≤ mean P X - gini P X) ∧
      (StrictSSD P X Y → mean P Y - gini P Y < mean P X - gini P X) := by sorry

end DualSSD.MeanRisk
