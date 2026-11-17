-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB31_original_risk_lower_cutoff_rightCont_stop
-- name    : AvramDividend.Classical.avram_gbB31_original_risk_lower_cutoff_rightCont_stop
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T17:59:19.277808+00:00
-- url     : https://prove2.me/theorems/6ccffefe-d0e9-4758-8ce8-0432153a221e
-- title:
--   Original continuous reserve lower cutoff is right-continuous filtration stopping time
-- statement:
--   For any original spectrally negative Levy process, original adapted dividend strategy D and continuous reserve trajectories riskProcess, construct the first lower-cutoff hit by H using the negative reserve process, and prove its stopping-time property for the right-continuous filtration. This is the exact shape of the Gaussian finite-cap floor-stopped clock needed in the physical-grid cash source.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_riskProcess_adapted
open MeasureTheory Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB31_original_risk_lower_cutoff_rightCont_stop
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (hRiskCont : ∀ ω, Continuous
      (fun t : ℝ≥0 => riskProcess X x D t ω))
    (S : Set ℝ≥0) (hS : S.Countable)
    (hDense : Dense S) (h0 : (0 : ℝ≥0) ∈ S)
    (H : ℝ≥0) (b : ℝ) :
    IsStoppingTime 𝓕.rightCont (fun ω : Ω =>
      WithTop.some (sInf ((Icc (0 : ℝ≥0) H ∩
        (fun t : ℝ≥0 => -(riskProcess X x D t ω)) ⁻¹'
          Ici (-b)) ∪ {H}))) := by sorry
