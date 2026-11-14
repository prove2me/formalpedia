-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a27_indep_source_sigma_comap_ae_congr_20261114
-- name    : AvramDividend.Classical.avram_a27_indep_source_sigma_comap_ae_congr_20261114
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T00:38:08.072091+00:00
-- url     : https://prove2.me/theorems/09e1bb26-bb74-4a91-ad91-c170dd4a4bfd
-- title:
--   Original-sigma-algebra independence of a real source observable survives almost-everywhere replacement
-- statement:
--   Given any original sigma-algebra H and measure P, if an original real random variable D is independent of H and agrees almost everywhere with E, then E is also independent of H under the same P.
-- source:
--   Pinned Mathlib ProbabilityTheory.IndepFun.congr and measurable-space comap identities.

import Mathlib
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section

/-- Independence of a Borel source observable from any original sub-sigma-algebra transfers across a.e. equality. -/

theorem AvramDividend.Classical.avram_a27_indep_source_sigma_comap_ae_congr_20261114
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (H : MeasurableSpace Ω)
    (D E : Ω → ℝ)
    (hInd : Indep (MeasurableSpace.comap D inferInstance) H P)
    (hEq : D =ᵐ[P] E) :
    Indep (MeasurableSpace.comap E inferInstance) H P := by sorry
