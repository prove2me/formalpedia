-- Prove2me | Theorems.Thm_EthierKurtz_one_dimensional_boundary_diffusion
-- name    : EthierKurtz.one_dimensional_boundary_diffusion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-21T06:08:32.163524+00:00
-- url     : https://prove2.me/theorems/0390b89a-bad2-42df-a10b-25b4c838aac1
-- title:
--   Theorem 1.1 — one-dimensional Feller generation with endpoint classification
-- statement:
--   For arbitrary finite or infinite endpoints, continuous interior coefficients with strictly positive diffusion coefficient, and regular-boundary parameters in [0,1], the exact graph determined by the scale and speed endpoint classification generates a positive conservative strongly continuous contraction semigroup on the compactified interval.
-- source:
--   Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986, Chapter 8, Section 1, Theorem 1.1, printed p. 367 (PDF p. 376), with equations (1.1)–(1.11), printed pp. 366–367, and the Feller convention on printed p. 166.

import Definitions.Def_EthierKurtz_IsStronglyContinuousContractionSemigroup
import Definitions.Def_EthierKurtz_diffusionBoundaryTests
import Definitions.Def_EthierKurtz_boundaryDiffusionGraph

open Filter MeasureTheory
open scoped Topology ENNReal

namespace EthierKurtz

/-- Ethier–Kurtz Chapter 8, Theorem 1.1. The graph itself, not merely a
restriction or its closure, is the full generator. Conservativity is written
as preservation of 1 on the compact extended interval. -/
theorem one_dimensional_boundary_diffusion
    (r₀ r₁ : EReal) (hends : r₀ < r₁)
    (a b : ℝ → ℝ) (r : ℝ)
    (hr : r₀ < (r : EReal) ∧ (r : EReal) < r₁)
    (ha : ContinuousOn a {x : ℝ | r₀ < (x : EReal) ∧ (x : EReal) < r₁})
    (hb : ContinuousOn b {x : ℝ | r₀ < (x : EReal) ∧ (x : EReal) < r₁})
    (hpos : ∀ x : ℝ, r₀ < (x : EReal) → (x : EReal) < r₁ → 0 < a x)
    (q : Fin 2 → ℝ)
    (hq : ∀ i : Fin 2,
      let e := if i = 0 then r₀ else r₁
      let uv := diffusionBoundaryTests a b r e
      uv.1 < ∞ → uv.2 < ∞ → q i ∈ Set.Icc (0 : ℝ) 1) :
    ∃ T : ℝ → C(Set.Icc r₀ r₁, ℝ) →L[ℝ] C(Set.Icc r₀ r₁, ℝ),
      IsStronglyContinuousContractionSemigroup T ∧
      (∀ t : ℝ, 0 ≤ t → ∀ f, (∀ x, 0 ≤ f x) → ∀ x, 0 ≤ T t f x) ∧
      (∀ t : ℝ, 0 ≤ t → T t 1 = 1) ∧
      (∀ f g, Tendsto (fun t : ℝ => t⁻¹ • (T t f - f))
        (𝓝[>] (0 : ℝ)) (𝓝 g) ↔ (f, g) ∈ boundaryDiffusionGraph r₀ r₁ a b r q) := by sorry
