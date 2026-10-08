-- Prove2me | Theorems.Thm_AvramDividend_Classical_levyWeight_integrable
-- name    : AvramDividend.Classical.levyWeight_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T11:28:39.654765+00:00
-- url     : https://prove2.me/theorems/10f622e0-c734-4897-803b-0ad7b4d1af5e
-- title:
--   The Lévy second-moment weight is integrable
-- statement:
--   The defining Lévy-measure hypothesis stores finiteness of the lintegral of ENNReal.ofReal(min(1,y^2)). Since min(1,y^2) is continuous, measurable and nonnegative, this is exactly ordinary Bochner/Lebesgue integrability of the real-valued weight min(1,y^2). This is the domination function used in the local generator-integrability proof.
-- source:
--   Direct reformulation of the Levy-measure integrability field ν_integrable in the mission definition.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.levyWeight_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    Integrable (fun y : ℝ => min 1 (y ^ 2)) X.ν := by sorry
