-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bridge20261123_A77_positive_atom_given_joint_temporal_vector_independence
-- name    : AvramDividend.Classical.avram_bridge20261123_A77_positive_atom_given_joint_temporal_vector_independence
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T18:17:43.810573+00:00
-- url     : https://prove2.me/theorems/59dec395-e30b-479f-adaa-69d594fe1ee9
-- title:
--   Original Lévy nonzero spatial marked-count atom law from joint time-vector independence and finite marked jump structure
-- statement:
--   The original source spectrally negative Lévy process has finite negative jump activity and at least two pairwise disjoint negative Borel mark sets. Assume the actual entire count vector for adjacent disjoint time windows is independent, for every split and horizon. Prove all nonzero spatial count-vector atom probabilities factor over the marks at a fixed time, exploiting finite activity, exclusion of simultaneous different-mark jumps, individual Poisson count intensities and a fine time-grid limit. The source vector temporal independence is independently Proved from the original shifted Lévy path and filtration adaptedness; it does not by itself imply spatial independence without this remaining fine-grid splitting argument.
-- source:
--   Original Avram c096 positive nonzero atom theorem reduced via b1190ab0 original finite marked-count adjacent vector independence and finite-activity source structure; no auxiliary probability space.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bridge20261123_A77_positive_atom_given_joint_temporal_vector_independence
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
          (Ioc s (s + T) ×ˢ B i)) P) :
    ∀ counts : Fin n → ℕ, counts ≠ (fun _ => 0) →
      P {ω : Ω | ∀ i, K i ω = counts i} =
        ∏ i : Fin n, P {ω : Ω | K i ω = counts i} := by sorry
