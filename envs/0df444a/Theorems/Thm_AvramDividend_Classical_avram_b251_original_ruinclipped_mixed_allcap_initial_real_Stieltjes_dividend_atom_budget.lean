-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b251_original_ruinclipped_mixed_allcap_initial_real_Stieltjes_dividend_atom_budget
-- name    : AvramDividend.Classical.avram_b251_original_ruinclipped_mixed_allcap_initial_real_Stieltjes_dividend_atom_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T21:36:46.18164+00:00
-- url     : https://prove2.me/theorems/9d560ff2-3938-4e47-ba19-51006898a9d6
-- title:
--   Original ruin-clipped allcap zero-clock dividend Stieltjes atom plus actual post-right-dividend caplinear potential bounded by initial original potential
-- statement:
--   For the original mixed Gaussian/negative-jump Lévy source X and actual admissible dividend D at either a finite or infinite admissible cap C, let the potential be the true candidate w or its linear continuation above the original finite cap. The original discounted dividend Stieltjes atom at the time-zero singleton [0,0], plus the actual post-right-dividend reserve potential V(x-rightLimit D(0)), is bounded by the original initial value V(x). This supplies the exact initial time-zero cash term omitted from the positive-time full-cell source ledger B248 and is essential for the genuine B236 inclusive Iic stopped cash inequality. It never assumes the initial dividend payment vanishes and uses no post-ruin state.
-- source:
--   Specialise Proved original any-cap closed full-Stieltjes signed correction to the true horizon T=0; original Lévy property X.X(0)=0 reduces the true original process to x, preserving the exact rightLimit D(0) initial right-dividend payment and allcap continuation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_05_any_cap_original_closed_full_stieltjes_signed_nonpos
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_b251_original_ruinclipped_mixed_allcap_initial_real_Stieltjes_dividend_atom_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (hq : 0 ≤ q) (C : ℝ≥0∞)
    (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) :
    let V : ℝ → ℝ := fun z =>
      if C = ⊤ then w z else
      if z ≤ C.toReal then w z else w C.toReal + (z - C.toReal)
    (∫⁻ t in Icc (0 : ℝ) (0 : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)).toReal +
    V (x - rightLimit D 0 ω) ≤ V x := by sorry
