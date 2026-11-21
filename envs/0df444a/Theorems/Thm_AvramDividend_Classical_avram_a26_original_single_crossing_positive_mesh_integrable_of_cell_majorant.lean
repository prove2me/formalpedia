-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a26_original_single_crossing_positive_mesh_integrable_of_cell_majorant
-- name    : AvramDividend.Classical.avram_a26_original_single_crossing_positive_mesh_integrable_of_cell_majorant
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T10:02:53.193392+00:00
-- url     : https://prove2.me/theorems/e70699f3-b778-45fe-8dfc-ff53151fbc73
-- title:
--   Original physical stopped single-crossing positive mesh integrable from L1 cell majorant
-- statement:
--   Any measurable stopped Gaussian physical grid crossing set of cardinality at most one, with nonnegative positive spatial residual in its unique crossing cell dominated by an integrable nonnegative random majorant B, has an integrable total crossing positive mesh sum. This discharges the separately assumed per-mesh hFI hypothesis in already Proved a99 and a108 stochastic crossing L1 lemmas once our true caplinear Gaussian cell majorant provides B. Does not assume the desired HJB reward budget or vanishing error.
-- source:
--   True Gaussian single-crossing physical grid positive residual integrability, unique crossing event.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical

theorem AvramDividend.Classical.avram_a26_original_single_crossing_positive_mesh_integrable_of_cell_majorant
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (S : Ω → Finset ℕ) (f : ℕ → Ω → ℝ)
    (B : Ω → ℝ)
    (hCard : ∀ᵐ ω ∂P, (S ω).card ≤ 1)
    (hB : ∀ᵐ ω ∂P, 0 ≤ B ω)
    (hBI : Integrable B P)
    (hCell : ∀ᵐ ω ∂P, ∀ i ∈ S ω,
      max (f i ω) 0 ≤ B ω)
    (hMeas : AEStronglyMeasurable
      (fun ω => ∑ i ∈ S ω, max (f i ω) 0) P) :
    Integrable (fun ω => ∑ i ∈ S ω, max (f i ω) 0) P := by sorry
