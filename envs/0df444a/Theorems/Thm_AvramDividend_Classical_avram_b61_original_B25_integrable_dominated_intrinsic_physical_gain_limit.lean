-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b61_original_B25_integrable_dominated_intrinsic_physical_gain_limit
-- name    : AvramDividend.Classical.avram_b61_original_B25_integrable_dominated_intrinsic_physical_gain_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T08:58:20.511671+00:00
-- url     : https://prove2.me/theorems/270b6aac-d766-4d05-9da0-8dcf8a02b3d7
-- title:
--   Original B25 intrinsic Gaussian or small-band physical mesh pointwise limit inherits integrability from its actual L1 dominating field
-- statement:
--   B25 provides an integrable dominating field and almost-sure convergence of physically formed Gaussian/small-band gain grids to MG/MJ. On the common full-measure set where every countable grid is dominated, the limit inherits the pointwise bound norm(MG)<=BG. Since the limit of a.e. strongly measurable fields is a.e. strongly measurable, the pinned generic Integrable.mono yields integrability of the original limiting intrinsic gain. This closes the additional MG/MJ integrability hypotheses in B60 without imposing L1 convergence on B25's signed error E.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_b61_original_B25_integrable_dominated_intrinsic_physical_gain_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (G : ℕ → Ω → ℝ) (MG BG : Ω → ℝ)
    (hMeas : ∀ k, AEStronglyMeasurable (G k) P)
    (hBG : Integrable BG P)
    (hDom : ∀ᵐ ω ∂P, ∀ k, ‖G k ω‖ ≤ BG ω)
    (hLim : ∀ᵐ ω ∂P,
      Tendsto (fun k => G k ω) atTop (𝓝 (MG ω))) :
    Integrable MG P := by sorry
