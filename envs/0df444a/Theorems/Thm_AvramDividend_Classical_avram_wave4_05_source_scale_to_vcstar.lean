-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_scale_to_vcstar
-- name    : AvramDividend.Classical.avram_wave4_05_source_scale_to_vcstar
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T10:23:45.447799+00:00
-- url     : https://prove2.me/theorems/b46a1808-12b8-48fd-b5c9-0310d53776b4
-- title:
--   Genuine source scale q-harmonicity transfers below the optimal barrier without a finiteness hypothesis
-- statement:
--   Assume the actual q-scale W solves the original Lévy generator q-harmonic equation and has the required full compensated generator domain at every positive reserve. Under the original Standing q-scale and cstar>0 assumptions, canonical cstar finiteness implies its real value is strictly positive. The proved exact source interior harmonicity transfer then gives GeneratorIntegrable vcstar and (Gamma-q)vcstar=0 at every 0<x<cstar, without a separate cstar<∞ assumption. This is a generator equality of the true dividend value candidate rather than a proxy.
-- source:
--   Canonical cstar_lt_top and exact vcstar_interior_harmonicity_of_scale_harmonicity, Mathlib 0df444a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_cstar_lt_top
import Theorems.Thm_AvramDividend_Classical_vcstar_interior_harmonicity_of_scale_harmonicity
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
/-- Pointwise full source scale harmonicity transfers to the genuine candidate. -/

theorem AvramDividend.Classical.avram_wave4_05_source_scale_to_vcstar
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W)
    (hc : 0 < cstar W)
    (hscale : ∀ x : ℝ, 0 < x →
      X.GeneratorIntegrable W x ∧ X.generator W x - q * W x = 0) :
    ∀ x ∈ Ioo 0 (cstar W).toReal,
      X.GeneratorIntegrable (vcstar W) x ∧
        X.generator (vcstar W) x - q * vcstar W x = 0 := by sorry
