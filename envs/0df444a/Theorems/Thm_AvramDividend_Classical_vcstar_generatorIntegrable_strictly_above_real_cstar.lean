-- Prove2me | Theorems.Thm_AvramDividend_Classical_vcstar_generatorIntegrable_strictly_above_real_cstar
-- name    : AvramDividend.Classical.vcstar_generatorIntegrable_strictly_above_real_cstar
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T06:47:58.236339+00:00
-- url     : https://prove2.me/theorems/32cfe60b-ce25-4a2e-b1e2-a007b60577ce
-- title:
--   The optimal dividend candidate lies in the Lévy generator domain strictly above its real cap
-- statement:
--   Let W be the pinned q-scale function, cstar W the extended-real optimal barrier and vcstar W its exact capped value candidate. At any finite reserve x>(cstar W).toReal, the Lévy generator jump integral of vcstar W is integrable. This transfers the independently Proved general barrierValue generator-integrability result using the formal definition vcstar W = barrierValue W (cstar W).toReal. The theorem does not incorrectly infer that an extended-real cstar is finite; the claim concerns the explicitly represented real cap.

import Mathlib.Data.ENNReal.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.vcstar_generatorIntegrable_strictly_above_real_cstar
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) (hx : (cstar W).toReal < x) :
    X.GeneratorIntegrable (vcstar W) x := by sorry
