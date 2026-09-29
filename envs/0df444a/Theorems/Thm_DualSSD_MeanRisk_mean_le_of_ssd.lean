-- Prove2me | Theorems.Thm_DualSSD_MeanRisk_mean_le_of_ssd
-- name    : DualSSD.MeanRisk.mean_le_of_ssd
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T00:07:06.627988+00:00
-- url     : https://prove2.me/theorems/0584ae26-a5f2-4a9d-84e7-110c60e3e3b9
-- title:
--   (4.1) — SSD dominance implies a larger mean
-- statement:
--   For integrable random variables $X$ and $Y$ on the same probability space,
--
--   $$X\succeq_{SSD}Y\ \Longrightarrow\ \mu_X\ge\mu_Y.$$
--
--   This commonly known necessary condition for SSD is one of the two inequalities combined in the efficiency argument for mean–risk models.
-- source:
--   Ogryczak, Ruszczyński, Dual Stochastic Dominance and Related Mean-Risk Models, SIAM J. Optim. 13 (2002), p. 69, eq. (4.1)

import Mathlib
import Definitions.Def_DualSSD_MeanRisk_gini

namespace DualSSD.MeanRisk

open MeasureTheory

/-- **(4.1)** (Ogryczak–Ruszczyński 2002, §4, p. 69). For integrable `X`, `Y`:
`X ⪰_SSD Y ⇒ μ_X ≥ μ_Y`. -/
theorem mean_le_of_ssd {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (hX : Integrable X P) (hY : Integrable Y P) :
    Shared.SSD P X Y → mean P Y ≤ mean P X := by sorry

end DualSSD.MeanRisk
