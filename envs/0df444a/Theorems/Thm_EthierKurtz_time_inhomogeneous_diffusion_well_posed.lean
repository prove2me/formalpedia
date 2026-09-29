-- Prove2me | Theorems.Thm_EthierKurtz_time_inhomogeneous_diffusion_well_posed
-- name    : EthierKurtz.time_inhomogeneous_diffusion_well_posed
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-21T06:05:24.927481+00:00
-- url     : https://prove2.me/theorems/2bbcdcad-c386-4f8e-a1dc-5054d5c63a32
-- title:
--   Theorem 1.7 — measurable-drift time-inhomogeneous diffusion well-posedness
-- statement:
--   For jointly measurable locally bounded coefficients with symmetric nonnegative covariance, bounded-time ellipticity at each spatial point, bounded-time uniform spatial continuity of the covariance, and the source quadratic covariance and one-sided drift growth bound, every initial probability law admits a measurable-process solution, and all such solutions have the same finite-dimensional distributions.
-- source:
--   Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986, Chapter 8, Section 1, Theorem 1.7 and equations (1.24)–(1.28), printed pp. 370–371 (PDF pp. 379–380); well-posedness convention from Chapter 4, printed pp. 173–174, 182; time-dependent convention from Chapter 5, printed pp. 290–295.

import Definitions.Def_EthierKurtz_diffusionOperator
import Definitions.Def_EthierKurtz_SolvesTimeInhomogeneousDiffusion

open MeasureTheory Filter
open scoped NNReal Topology ContDiff

namespace EthierKurtz

/-- Existence for every initial probability law and uniqueness of all finite
-dimensional distributions among measurable-process solutions on arbitrary
probability spaces. Ellipticity is uniform in bounded time at each fixed x;
spatial continuity of a is uniform over the same time interval. Drift needs
only Borel measurability, local boundedness, and the one-sided growth bound. -/
theorem time_inhomogeneous_diffusion_well_posed (d : ℕ) [NeZero d]
    (a : ℝ≥0 × EuclideanSpace ℝ (Fin d) →
      EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (b : ℝ≥0 × EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (ha : Measurable a) (hb : Measurable b)
    (hsym : ∀ z u v, inner ℝ (a z u) v = inner ℝ u (a z v))
    (hnonneg : ∀ z u, 0 ≤ inner ℝ u (a z u))
    (hlocal : ∀ C : Set (ℝ≥0 × EuclideanSpace ℝ (Fin d)), IsCompact C →
      ∃ M : ℝ, ∀ z ∈ C, ‖a z‖ ≤ M ∧ ‖b z‖ ≤ M)
    (helliptic : ∀ (x : EuclideanSpace ℝ (Fin d)) (T : ℝ≥0), 0 < T →
      ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ≥0, t ≤ T →
        ∀ θ : EuclideanSpace ℝ (Fin d), ‖θ‖ = 1 →
          ε ≤ inner ℝ θ (a (t, x) θ))
    (hspatial : ∀ (x : EuclideanSpace ℝ (Fin d)) (T : ℝ≥0), 0 < T →
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ y : EuclideanSpace ℝ (Fin d), ‖y - x‖ < δ →
          ∀ t : ℝ≥0, t ≤ T → ‖a (t, y) - a (t, x)‖ < ε)
    (hgrowth : ∃ K : ℝ, ∀ (t : ℝ≥0) (x : EuclideanSpace ℝ (Fin d)),
      ‖a (t, x)‖ ≤ K * (1 + ‖x‖ ^ 2) ∧
      inner ℝ x (b (t, x)) ≤ K * (1 + ‖x‖ ^ 2))
    (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ] :
    ∃ (Ω : Type) (m : MeasurableSpace Ω),
      letI : MeasurableSpace Ω := m
      ∃ P : Measure Ω, IsProbabilityMeasure P ∧
        ∃ X : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d),
          SolvesTimeInhomogeneousDiffusion a b μ P X ∧
          ∀ (Ω' : Type) (m' : MeasurableSpace Ω'),
            letI : MeasurableSpace Ω' := m'
            ∀ Q : Measure Ω', IsProbabilityMeasure Q →
              ∀ Y : ℝ≥0 → Ω' → EuclideanSpace ℝ (Fin d),
                SolvesTimeInhomogeneousDiffusion a b μ Q Y →
                ∀ (n : ℕ) (t : Fin n → ℝ≥0),
                  Measure.map (fun w i => X (t i) w) P =
                    Measure.map (fun w i => Y (t i) w) Q := by sorry
