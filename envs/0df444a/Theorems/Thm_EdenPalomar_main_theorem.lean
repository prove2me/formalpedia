-- Prove2me | Theorems.Thm_EdenPalomar_main_theorem
-- name    : EdenPalomar.main_theorem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:53:00.483145+00:00
-- url     : https://prove2.me/theorems/9f82d26e-3c9a-4ae6-80f9-3ffe0405f226
-- title:
--   Eden Palomar: main theorem
-- statement:
--   Theorem 1.1, including the forward ODE, uniqueness, differentiability,
--   invertibility, dimension attainment and existence of exponents. The exact
--   angular formula strengthens the asserted absence of periodic orbits.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/PalomarSolution.lean#L124-L162
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/PalomarSolution.lean#L124-L162

import Definitions.Def_Eden_Solution
import Definitions.Def_PalomarSolution
import Theorems.Thm_EdenVerified_main_theorem

set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open EdenPalomar

theorem EdenPalomar.main_theorem (c : ℝ) (hc : 4 < c) :
    ∃ φ : ℝ → PhaseSpace → PhaseSpace,
    (∀ p, φ 0 p = p ∧ ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (fun τ => φ τ p) (vectorField c (φ t p)) t) ∧
    (∀ (p : PhaseSpace) (f : ℝ → PhaseSpace),
      ContinuousOn f (Ici 0) →
      (∀ t : ℝ, 0 ≤ t → HasDerivWithinAt f (vectorField c (f t)) (Ici t) t) →
      f 0 = p → EqOn f (fun t => φ t p) (Ici 0)) ∧
    (∀ (s t : ℝ), 0 ≤ s → 0 ≤ t → ∀ p, φ (s + t) p = φ t (φ s p)) ∧
    (∀ t : ℝ, 0 ≤ t → ContDiff ℝ 1 (φ t)) ∧
    (∀ t : ℝ, 0 ≤ t → ∀ p, Function.Bijective (fderiv ℝ (φ t) p)) ∧
    IsGlobalAttractor φ attractor ∧
    (∀ p, divergence c p = 4 - c - 6 * (radiusSq₁ p - 1) ^ 2 -
      6 * (radiusSq₂ p - 1) ^ 2 ∧ divergence c p ≤ 4 - c ∧ 4 - c < 0) ∧
    (4 < 4 + 4 / c ∧ 4 + 4 / c < 5) ∧
    (∀ t : ℝ, 0 < t →
      IsGreatest (finiteTimeDimension φ t '' attractor) (4 + 4 / c) ∧
      {p ∈ attractor | finiteTimeDimension φ t p = 4 + 4 / c} = torus) ∧
    (∀ p ∈ attractor, ∀ i : Fin 5,
      Tendsto (fun t : ℝ => Real.log ((fderiv ℝ (φ t) p).toLinearMap.singularValues i) / t)
        atTop (𝓝 (lyapunovExponent φ p i))) ∧
    (globalLyapunovDimension φ attractor = 4 + 4 / c) ∧
    IsGreatest (asymptoticDimension φ '' attractor) (4 + 4 / c) ∧
    ({p ∈ attractor | asymptoticDimension φ p = 4 + 4 / c} = torus) ∧
    IsGreatest (asymptoticDimension φ '' periodicEquilibriumSet c φ) 3 ∧
    (∀ t : ℝ, 0 < t →
      IsGreatest (finiteTimeDimension φ t '' periodicEquilibriumSet c φ) 3) ∧
    (∀ (t : ℝ) (p : PhaseSpace), p ∈ torus → φ t p ∈ torus) ∧
    (∀ p ∈ torus, ∀ t : ℝ, 0 < t → φ t p ≠ p) ∧
    (∀ t θ₁ θ₂ : ℝ, φ t (torusPoint θ₁ θ₂) =
      torusPoint (θ₁ + t) (θ₂ + Real.sqrt 2 * t)) ∧
    (∀ p ∈ attractor, Tendsto (fun t : ℝ => finiteTimeDimension φ t p)
      atTop (𝓝 (asymptoticDimension φ p))) ∧
    (∀ t : ℝ, 0 < t → ∀ p,
      IsGreatest (admissibleDimensions φ t p) (finiteTimeDimension φ t p)) := by sorry
