-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_closed_grid_true_survival_terminal
-- name    : AvramDividend.Classical.avram_p3_bv_original_closed_grid_true_survival_terminal
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T20:11:04.703698+00:00
-- url     : https://prove2.me/theorems/322a98f8-a550-43d9-8f15-750836956465
-- title:
--   Exact original stopped BV closed grid Stieltjes reward with genuine controlled-surplus verification terminal
-- statement:
--   For the genuine original controlled Levy process at finite/infinite cap, every admissible monotone chronological finite grid before ruin satisfies a discounted reward budget with the true post-rightpayment w-survival terminal, complete closed-horizon Stieltjes cash (time-zero atom included), and explicit cap-linear source increment terms. The abstract verification extension at the terminal is eliminated by source-exact cap contact.
-- source:
--   Composition of new Proved dca893c2 (physical original grid cap-linear Stieltjes budget) and Proved 37425aad (actual original book postpayment V=w at cap).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_explicit_caplinear_source_mesh
import Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_public_original_anycap_book_postpayment_V_eq_w

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/- The finite original controlled grid pays true Stieltjes cash and keeps
the original w terminal at the closed final grid clock, at either cap. -/

theorem AvramDividend.Classical.avram_p3_bv_original_closed_grid_true_survival_terminal
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hxc : ENNReal.ofReal x ≤ C)
    (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (u : ℕ → ℝ≥0) (n : ℕ)
    (hu : Monotone u) (hu0 : u 0 = 0)
    (hPre : ∀ i : ℕ, i < n →
      u (i + 1) = 0 ∨
        (u (i + 1) : ℝ≥0∞) < ruinTime X x D ω) :
    let V : ℝ → ℝ := fun z =>
      if C = ⊤ then w z else if z ≤ C.toReal then w z
      else w C.toReal + (z - C.toReal)
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    let Y : ℝ≥0 → ℝ := fun t =>
      x + X.X t ω - rightLimit D t ω
    let Z : ℕ → ℝ := fun i =>
      x + X.X (u (i + 1)) ω - rightLimit D (u i) ω
    E (u n) * w (Y (u n)) +
      (∫⁻ s in Icc (0 : ℝ) (u n : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal ≤
      V x +
        ∑ i ∈ Finset.range n,
          ((E (u (i + 1)) - E (u i)) * V (Y (u (i + 1))) +
            E (u i) * (V (Z i) - V (Y (u i)))) := by sorry
