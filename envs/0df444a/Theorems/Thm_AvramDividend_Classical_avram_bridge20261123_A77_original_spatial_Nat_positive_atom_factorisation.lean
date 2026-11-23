-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bridge20261123_A77_original_spatial_Nat_positive_atom_factorisation
-- name    : AvramDividend.Classical.avram_bridge20261123_A77_original_spatial_Nat_positive_atom_factorisation
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T17:45:32.884028+00:00
-- url     : https://prove2.me/theorems/c0960683-ef39-4f15-bba4-e15bf5bcb83d
-- title:
--   Original spectrally negative Lévy disjoint negative-Borel joint count cylinder factorisation for nonzero count vectors
-- statement:
--   For any nonzero prescribed finite Nat count vector on the unchanged original spectrally negative Levy source, finite negative Levy activity, disjoint Borel mark sets, and exact almost-sure Nat count representatives, prove the probability of the joint count event factors into the product of its marginals. This is the essential positive-count Poisson splitting law. All-zero vectors are treated by the separate Proved physical void-event factorisation. A direct proof should exploit true original jump point process structure and time-grid count limits, not assert that marginal Poisson laws imply joint independence.
-- source:
--   Original A77 spatial independence root 3ece8183; original A27 disjoint marked Borel void product 286edb08; accepted generic finite joint atom criterion 4123dd92.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bridge20261123_A77_original_spatial_Nat_positive_atom_factorisation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (t : ℝ≥0) (n : ℕ) (B : Fin n → Set ℝ)
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
