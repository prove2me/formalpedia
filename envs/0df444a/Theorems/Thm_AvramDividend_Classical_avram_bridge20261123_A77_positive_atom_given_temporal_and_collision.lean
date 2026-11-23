-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bridge20261123_A77_positive_atom_given_temporal_and_collision
-- name    : AvramDividend.Classical.avram_bridge20261123_A77_positive_atom_given_temporal_and_collision
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T18:27:00.643025+00:00
-- url     : https://prove2.me/theorems/d11a7cb2-2bf5-4e95-ab43-9ea6b2f0345b
-- title:
--   Original spatial marked-Poisson nonzero joint count atoms from independent time vectors and quadratic collision control
-- statement:
--   Original finite-negative-activity Lévy source with at least two disjoint negative Borel mark sets, and genuine Nat-valued original physical counts. Assume full physical count-vector independence in adjacent time intervals and an O(delta²) bound for probability of two or more negative jumps in their union over short intervals. Derive factorisation of every nonzero marked count-vector joint point probability through a marked small-time grid limit and compound Poisson multivariate limit. The two hypotheses are separately proved for the original source: original vector temporal independence and original union two-jump collision. This remaining theorem requires the actual first-order distribution over the distinct marks and limit argument, not independence of marginal Poisson laws.
-- source:
--   Original A77 positive atom source af6e786e, and Proved physical source temporal b1190ab0 / union twojump collision 4ced9f55; same original X, P and ν.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bridge20261123_A77_positive_atom_given_temporal_and_collision
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
          (Ioc 0 t ×ˢ B i)).toReal)
    (hTemporal : ∀ (s T : ℝ≥0),
      IndepFun
      (fun ω : Ω => fun i : Fin n =>
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 s ×ˢ B i))
      (fun ω : Ω => fun i : Fin n =>
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc s (s + T) ×ˢ B i)) P)
    (hCollision : ∀ δ : ℝ≥0,
      (P {ω : Ω | (2 : ℝ) ≤
      (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 δ ×ˢ (⋃ i, B i))).toReal}).toReal ≤
      (((δ : ℝ≥0∞) * X.ν (⋃ i, B i)).toReal) ^ 2 / 2) :
    ∀ counts : Fin n → ℕ, counts ≠ (fun _ => 0) →
      P {ω : Ω | ∀ i, K i ω = counts i} =
        ∏ i : Fin n, P {ω : Ω | K i ω = counts i} := by sorry
