-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_closed_cash_interior_w_commutator_budget
-- name    : AvramDividend.Classical.avram_p3_2_original_closed_cash_interior_w_commutator_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T00:18:17.933583+00:00
-- url     : https://prove2.me/theorems/7266a3c5-4291-4183-9315-d8774b711877
-- title:
--   Original stopped BV cash/source budget uses true w mixed commutator on cap-safe physical drift grid
-- statement:
--   For actual original BV spectrally negative Lévy X and admissible capped dividend control D, a zero-start preruin physical grid with each frozen drift-upshift within the closed cap has its true discounted Stieltjes cash and terminal w bounded by initial w plus cap-linear drift, true original negative-jump w source kernel and true w mixed-J commutator. All source variables are physical X.X and rightLimit D and the cap at left endpoints is derived from admissibility. This is the exact conditional interface for F2's w mixed-J mesh-error theorem.
-- source:
--   Composition of Accepted P3-2 original closed cash/source grid 4338db7f, original physical cap-safe mixed commutator 51bae427, and admissible closed cap d88fd858.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_closed_cash_wjump_commutator_budget
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_physical_mixed_commutator_eq_w_grid
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_postrightpayment_reserve_closed_cap

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p3_2_original_closed_cash_interior_w_commutator_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (hx : 0 ≤ x) (C : ℝ≥0∞) (hC : 0 < C)
    (hxc : ENNReal.ofReal x ≤ C)
    (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) :
    let V : ℝ → ℝ := fun z =>
      if C = ⊤ then w z else if z ≤ C.toReal then w z
      else w C.toReal + (z - C.toReal)
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    ∀ᵐ ω ∂P, ∀ (u : ℕ → ℝ≥0) (n : ℕ),
      Monotone u → u 0 = 0 →
      (∀ i : ℕ, i < n →
        u (i + 1) = 0 ∨
          (u (i + 1) : ℝ≥0∞) < ruinTime X x D ω) →
      (∀ i : ℕ, i < n →
        C = ⊤ ∨ x + X.X (u i) ω - rightLimit D (u i) ω +
          (((u (i + 1) : ℝ) - (u i : ℝ)) * X.drift) ≤ C.toReal) →
    let Y : ℝ≥0 → ℝ := fun t =>
      x + X.X t ω - rightLimit D t ω
    let z : ℕ → ℝ := fun i => Y (u i)
    let c : ℕ → ℝ := fun i =>
      ((u (i + 1) : ℝ) - (u i : ℝ)) * X.drift
    let j : ℕ → ℝ := fun i =>
      ∑' v : ℝ≥0, if u i < v ∧ v ≤ u (i + 1) then
        Function.leftLim (fun t : ℝ≥0 => X.X t ω) v - X.X v ω
      else 0
    E (u n) * w (Y (u n)) +
      (∫⁻ s in Icc (0 : ℝ) (u n : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal ≤
      w x +
        (∑ i ∈ Finset.range n,
          (E (u (i + 1)) - E (u i)) * V (Y (u (i + 1)))) +
        ((∑ i ∈ Finset.range n,
          E (u i) * (V (z i + c i) - V (z i))) +
         (∑ i ∈ Finset.range n,
          E (u i) * (w (z i - j i) - w (z i))) +
         (∑ i ∈ Finset.range n,
          E (u i) * (w (z i + c i - j i) - w (z i + c i) -
            w (z i - j i) + w (z i)))) := by sorry
