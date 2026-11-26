-- Prove2me | Theorems.Thm_EdenVerified_main_theorem
-- name    : EdenVerified.main_theorem
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T15:07:50.048345+00:00
-- url     : https://prove2.me/theorems/e003141d-36a6-575d-82ee-5f8e3cb56ff3
-- title:
--   Eden Verified: main theorem
-- statement:
--   The joint main theorem, including the ambient ODE and its uniqueness. All time
--   variables are real; all derivatives use the ambient Euclidean norm.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L24-L88
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L24-L88

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.main_theorem (c : ℝ) (hc : 4 < c) :
    (∀ p : PhaseSpace, evolution c 0 p = p ∧
      ∀ t : ℝ, 0 ≤ t → HasDerivAt (fun τ => evolution c τ p)
        (vectorField c (evolution c t p)) t) ∧
    (∀ (p : PhaseSpace) (f : ℝ → PhaseSpace),
      ContinuousOn f (Ici 0) →
      (∀ t : ℝ, 0 ≤ t → HasDerivWithinAt f (vectorField c (f t)) (Ici t) t) →
      f 0 = p → EqOn f (fun t => evolution c t p) (Ici 0)) ∧
    (∀ (s t : ℝ), 0 ≤ s → 0 ≤ t → ∀ p : PhaseSpace,
      evolution c (s + t) p = evolution c t (evolution c s p)) ∧
    (∀ t : ℝ, 0 ≤ t → ContDiff ℝ 1 (evolution c t)) ∧
    (∀ t : ℝ, 0 ≤ t → ∀ p : PhaseSpace,
      Function.Bijective (fderiv ℝ (evolution c t) p)) ∧
    IsGlobalAttractor c attractor ∧
    (∀ p : PhaseSpace,
      divergence c p = 4 - c - 6 * (radiusSq₁ p - 1) ^ 2 -
        6 * (radiusSq₂ p - 1) ^ 2 ∧ divergence c p ≤ 4 - c ∧ 4 - c < 0) ∧
    (4 < 4 + 4 / c ∧ 4 + 4 / c < 5) ∧
    (∀ t : ℝ, 0 < t →
      IsGreatest (finiteTimeDimension c t '' attractor) (4 + 4 / c) ∧
      {p ∈ attractor | finiteTimeDimension c t p = 4 + 4 / c} = torus) ∧
    (∀ p ∈ attractor, ∀ i : Fin 5,
      Tendsto (fun t : ℝ => Real.log
        ((fderiv ℝ (evolution c t) p).toLinearMap.singularValues i) / t)
        atTop (𝓝 (lyapunovExponent c p i))) ∧
    (globalLyapunovDimension c attractor = 4 + 4 / c) ∧
    IsGreatest (asymptoticDimension c '' attractor) (4 + 4 / c) ∧
    ({p ∈ attractor | asymptoticDimension c p = 4 + 4 / c} = torus) ∧
    IsGreatest (asymptoticDimension c '' periodicEquilibriumSet c) 3 ∧
    (∀ t : ℝ, 0 < t →
      IsGreatest (finiteTimeDimension c t '' periodicEquilibriumSet c) 3) ∧
    (∀ (t : ℝ) (p : PhaseSpace), p ∈ torus → evolution c t p ∈ torus) ∧
    (∀ p ∈ torus, ∀ t : ℝ, 0 < t → evolution c t p ≠ p) ∧
    (∀ t θ₁ θ₂ : ℝ, evolution c t (torusPoint θ₁ θ₂) =
      torusPoint (θ₁ + t) (θ₂ + Real.sqrt 2 * t)) ∧
    (∀ p ∈ attractor, Tendsto (fun t : ℝ => finiteTimeDimension c t p)
      atTop (𝓝 (asymptoticDimension c p))) := by sorry
