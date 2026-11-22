-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jp23_topcap_physical_fullnegative_mark_fibre_L1
-- name    : AvramDividend.Classical.avram_jp23_topcap_physical_fullnegative_mark_fibre_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T23:28:06.868085+00:00
-- url     : https://prove2.me/theorems/50e9bf07-8b7c-4a17-a05f-03d209176585
-- title:
--   Quantitative true physical topcap negative mark L1 at every stopped time-space fibre
-- statement:
--   At C=top and finite negative Levy activity, the genuine stopped physical nonlinear fullnegative H(t,omega,z) on the true prepayment left reserve and ruin clock has finite absolute mark integral with respect to the ACTUAL negative source Levy intensity X.ν|{z<0} for every physical time and path. More precisely bound the marked fibre lintegral of |H| by X.ν(z<0) times exp(-qt)w(Y(t,omega)), with no spatial cut, no bounded variation assumption, and no synthetic jump measure. Obtain directly from the separately Proved source envelope avram_jp23_topcap_fullnegative_H_absolute_source_envelope and the finite source negative rate. The unresolved global J L1 proof must integrate this bound over physical time and P, control the true expected prepayment occupation and invoke original compensated Campbell/Mecke; this theorem supplies only the genuine mark-fibre L1 bridge to that problem.
-- source:
--   Original topcap root d3408f6b, original negative J child b60f135e; direct proved kernel envelope 0f2256b5; actual finite negative rate hFiniteActivity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem AvramDividend.Classical.avram_jp23_topcap_physical_fullnegative_mark_fibre_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hTop : C = ⊤)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (q : ℝ) (σ : Ω → ℝ≥0)
    (hFiniteActivity : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
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
    ∀ (t : ℝ≥0) (ω : Ω),
      (∫⁻ z : ℝ, ENNReal.ofReal (‖H ((t, ω), z)‖)
        ∂(X.ν.restrict (Iio (0 : ℝ)))) ≤
          ENNReal.ofReal (Real.exp (-(q * (t : ℝ))) * w (Y (t, ω))) *
            X.ν (Iio (0 : ℝ)) ∧
      (∫⁻ z : ℝ, ENNReal.ofReal (‖H ((t, ω), z)‖)
        ∂(X.ν.restrict (Iio (0 : ℝ)))) < ⊤ := by sorry
