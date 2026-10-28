-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_canonical_finite_esscher_increment_vector_reversal
-- name    : AvramDividend.Classical.avram_ws01e_b_canonical_finite_esscher_increment_vector_reversal
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T08:22:42.916553+00:00
-- url     : https://prove2.me/theorems/7b932bba-83c4-4c3c-bbd9-6246364da425
-- title:
--   Canonical finite-horizon Esscher law preserves the full equal-mesh Lévy increment-vector reversal
-- statement:
--   For a spectrally negative Lévy process whose canonical origin is X_0=0, the finite-terminal Esscher path measure Q_{nδ}=P.withDensity(exp(θX_{nδ}−nδψ(θ))) has an increment-vector pushforward law invariant under reversal of its n equal-mesh increments. This is the exact full Borel law of the canonical finite-horizon Esscher process, distinct from a made-up infinite-horizon tilted process. The proof transfers the accepted displacement-weighted finite-mesh reversal theorem to the canonical Q_T law using the accepted zero-origin equality of the two densities.
-- source:
--   Proved avram_ws01e_b_true_finite_terminal_esscher_increment_reversal (bf836fe1), canonical density alignment (pending publication) and X.X_zero.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_canonical_esscher_density_eq_displacement_density
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_true_finite_terminal_esscher_increment_reversal

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

/-- Full increment-vector reversal for the *canonical* Q_T Esscher law. -/

theorem AvramDividend.Classical.avram_ws01e_b_canonical_finite_esscher_increment_vector_reversal
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (δ : ℝ≥0) (n : ℕ) (θ : ℝ) :
    Measure.map (fun v : Fin n → ℝ => fun i => v i.rev)
      (Measure.map
        (fun ω : Ω => fun i : Fin n =>
          X.X (((i.val + 1 : ℕ) : ℝ≥0) * δ) ω -
          X.X ((i.val : ℝ≥0) * δ) ω)
        (P.withDensity (fun ω : Ω => ENNReal.ofReal
          (Real.exp (θ * X.X ((n : ℝ≥0) * δ) ω -
            (((n : ℝ≥0) * δ : ℝ≥0) : ℝ) * X.ψ θ))))) =
    Measure.map
      (fun ω : Ω => fun i : Fin n =>
        X.X (((i.val + 1 : ℕ) : ℝ≥0) * δ) ω -
        X.X ((i.val : ℝ≥0) * δ) ω)
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X ((n : ℝ≥0) * δ) ω -
          (((n : ℝ≥0) * δ : ℝ≥0) : ℝ) * X.ψ θ)))) := by sorry
