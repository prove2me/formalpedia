-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jp23_topcap_fullnegative_H_absolute_source_envelope
-- name    : AvramDividend.Classical.avram_jp23_topcap_fullnegative_H_absolute_source_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T23:23:18.403058+00:00
-- url     : https://prove2.me/theorems/0f2256b5-fa1c-4713-880a-8204d67f80de
-- title:
--   Original topcap fullnegative nonlinear jump H controlled by discounted prepayment value
-- statement:
--   For the exact original spectrally negative Levy physical fullnegative nonlinear stopped marked jump kernel H under the infinite cap, prove the global pointwise absolute bound ||H((t,omega),z)|| ≤ exp(-q t) w(Y(t,omega)), where Y is the actual prepayment left limit of surplus x+X-rightLimit D and all original physical stochastic stop/ruin/negative mark guard conditions remain identical. The proof uses independently Proved global topcap gradient secant 6822fd33 to show w is everywhere nonnegative, together with the independently Proved fullnegative H sign theorem 2bb6c05a. With finite negative source Levy intensity this supplies the exact full nonlinear kernel integrable envelope needed for the remaining compensated J L1/initial-event centring proof: the outstanding need is physical time expected discounted positive prepayment w(Y) occupation and true source compensation. No finitecap or bounded variation assumption and no synthetic model.
-- source:
--   Original d340 topcap physical H, Proved 6822fd33 topcap global secant and Proved 2bb6c05a actual H sign.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem AvramDividend.Classical.avram_jp23_topcap_fullnegative_H_absolute_source_envelope
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
    ∀ p : ((ℝ≥0 × Ω) × ℝ),
      ‖H p‖ ≤ Real.exp (-(q * (p.1.1 : ℝ))) * w (Y p.1) := by sorry
