-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bridge20261123_A77_positive_atom_at_least_two_marks
-- name    : AvramDividend.Classical.avram_bridge20261123_A77_positive_atom_at_least_two_marks
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T18:05:44.688126+00:00
-- url     : https://prove2.me/theorems/af6e786e-cf2c-41f5-913f-dc3ccf2e2572
-- title:
--   Original Lévy positive joint atom factorisation for at least two disjoint negative Borel marks
-- statement:
--   For the original finite-activity spectrally negative Lévy process, at least two disjoint negative Borel mark sets, and Nat-valued physical jump count representatives identified almost surely with the original source, establish nonzero joint count-vector probability factorisation. Families with at most one mark are discharged automatically by independence of subsingleton index families. Proving this is the remaining genuine spatial Poisson splitting obligation.
-- source:
--   Original A77 positive atom theorem c0960683-ef39-4f15-bba4-e15bf5bcb83d; exact original source.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bridge20261123_A77_positive_atom_at_least_two_marks
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (t : ℝ≥0) (n : ℕ) (hn : 2 ≤ n) (B : Fin n → Set ℝ)
    (hMeas : ∀ i, MeasurableSet (B i))
    (hNeg : ∀ i, B i ⊆ Iio (0 : ℝ))
    (hPair : ∀ i j, i ≠ j → Disjoint (B i) (B j))
    (K : Fin n → Ω → ℕ)
    (hK : ∀ i, Measurable (K i))
    (hReal : ∀ᵐ ω ∂P, ∀ i,
      (K i ω : ℝ) =
        (((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 t ×ˢ B i)).toReal) :
    ∀ counts : Fin n → ℕ, counts ≠ (fun _ => 0) →
      P {ω : Ω | ∀ i, K i ω = counts i} =
        ∏ i : Fin n, P {ω : Ω | K i ω = counts i} := by sorry
