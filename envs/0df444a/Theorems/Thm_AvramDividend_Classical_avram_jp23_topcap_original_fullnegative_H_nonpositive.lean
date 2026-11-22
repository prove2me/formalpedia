-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jp23_topcap_original_fullnegative_H_nonpositive
-- name    : AvramDividend.Classical.avram_jp23_topcap_original_fullnegative_H_nonpositive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T23:10:49.21261+00:00
-- url     : https://prove2.me/theorems/2bb6c05a-dc8c-4925-be97-f069894616ce
-- title:
--   Original topcap physical fullnegative nonlinear jump kernel is nonpositive
-- statement:
--   For the actual spectrally negative Levy source, original controlled prepayment reserve left-limit Y, ruinTime and original source fullnegative nonlinear jump kernel H, prove that H is pointwise nonpositive at C=top. Derive via the already Proved topcap gradient >= 1 global secant theorem 6822fd33, since w is monotone for positive reserve and zero for negative surplus. Preserve original marks and time/ruin masks, no finitecap assumption. The theorem supplies the sign required to control the actual stopped compensated jump sum by its predictable compensator; J integrability and initial centring remain separate mathematical obligations. It is to be imported into the root-connected Avram d3408f6b negative-mark branch.
-- source:
--   Proved avram_gledger29_topcap_secant_without_contdiff 6822fd33; exact source d3408f6b physical H at C=top.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem AvramDividend.Classical.avram_jp23_topcap_original_fullnegative_H_nonpositive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hTop : C = ⊤)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (q : ℝ) (σ : Ω → ℝ≥0) :
    let Y : ℝ≥0 × Ω → ℝ := fun p =>
      Function.leftLim
        (fun r : ℝ≥0 => x + X.X r p.2 - rightLimit D r p.2) p.1
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      if 0 < p.1.1 ∧ p.1.1 ≤ σ p.1.2 ∧
          (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 ∧
          0 ≤ Y p.1 ∧ ENNReal.ofReal (Y p.1) ≤ C ∧ p.2 < 0 then
        Real.exp (-(q * (p.1.1 : ℝ))) *
          (w (Y p.1 + p.2) - w (Y p.1))
      else 0
    ∀ p : ((ℝ≥0 × Ω) × ℝ), H p ≤ 0 := by sorry
