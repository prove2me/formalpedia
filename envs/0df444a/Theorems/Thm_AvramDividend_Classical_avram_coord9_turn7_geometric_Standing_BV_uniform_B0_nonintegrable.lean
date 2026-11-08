-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_coord9_turn7_geometric_Standing_BV_uniform_B0_nonintegrable
-- name    : AvramDividend.Classical.avram_coord9_turn7_geometric_Standing_BV_uniform_B0_nonintegrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T23:33:36.335381+00:00
-- url     : https://prove2.me/theorems/e32fd526-7979-4d29-9cfc-e962b49db59f
-- title:
--   Geometric singular reserve forces original Standing BV first-cell nonintegrability
-- statement:
--   A measure-preserving geometric index and the exact source HJB profile imply nonintegrability of the original uniform-grid first generator cell for an actual Standing BV Levy process. This closes the scalar-to-original-cell implication and isolates the separate existence of a source-exact Levy countermodel.
-- source:
--   Source-exact composition of Proved geometric transport 926832da and Standing BV first-row 4175c1b5.

import Mathlib.Topology.Order.LeftRightLim
import Mathlib.Probability.Distributions.Geometric
import Theorems.Thm_AvramDividend_Classical_avram_a19_singular_geometric_transport_nonintegrable
import Theorems.Thm_AvramDividend_Classical_avram_coord9_turn6_original_Standing_BV_uniform_B0_nonintegrable
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A geometric law for the post-dividend reserve supplies the non-L1
    profile needed for the original Standing BV first cell. -/

theorem AvramDividend.Classical.avram_coord9_turn7_geometric_Standing_BV_uniform_B0_nonintegrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hBV : X.BoundedVariation)
    (q T x : ℝ) (hT : 0 < T)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hruin : ∀ ω, (0 : ℝ≥0∞) < ruinTime X x D ω)
    (hpositive : ∀ ω, 0 < x - rightLimit D 0 ω)
    (hcap : ∀ ω, ENNReal.ofReal (x - rightLimit D 0 ω) < C)
    (hmeas : AEStronglyMeasurable (fun ω =>
      X.generator w (x - rightLimit D 0 ω) -
        q * w (x - rightLimit D 0 ω)) P)
    (p : unitInterval) (hp : p != 0) (hhalf : (p : ℝ) = 1 / 2)
    (K : Ω → ℕ) (hK : MeasurePreserving K P (geometricMeasure p))
    (y : ℕ → ℝ)
    (hy : ∀ k, 0 < y k)
    (hsmall : ∀ k, y k ≤ 1 / 16)
    (hpower : ∀ k, y k ≤ 1 / ((2 : ℝ) ^ k) ^ 2)
    (hprofile : ∀ᵐ ω ∂P,
      X.generator w (x - rightLimit D 0 ω) -
        q * w (x - rightLimit D 0 ω) =
      (3 : ℝ) + y (K ω) - 4 * Real.sqrt (y (K ω)) -
        2 / Real.sqrt (y (K ω)))
    (u : ℕ → ℕ → ℝ≥0) (B : ℕ → Ω → ℝ)
    (hgrid0 : ∀ n, u n 0 = 0)
    (huniform : ∀ n i, (u n i : ℝ) = T * (i : ℝ) / ((n : ℝ) + 2))
    (hB : ∀ n ω,
      let Z : ℕ → ℝ := fun i => Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
      B n ω =
        (∑ i ∈ Finset.range (n + 1),
          if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
              0 < Z i ∧ ENNReal.ofReal (Z i) < C then
            Real.exp (-(q * (u n i : ℝ))) *
              (X.generator w (Z i) - q * w (Z i)) *
              ((u n (i + 1) : ℝ) - (u n i : ℝ))
          else 0) +
        (let J : ℝ≥0 → ℝ := fun t =>
            ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
              Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
            else 0
         let R : ℝ≥0 → ℝ := fun t =>
           ((t : ℝ) * X.drift - X.X t ω) - J t
         ∑ i ∈ Finset.range (n + 1),
           (if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
               0 < Z i ∧ ENNReal.ofReal (Z i) < C then
             Real.exp (-(q * (u n i : ℝ))) * deriv w (Z i)
            else 0) * (R (u n i) - R (u n (i + 1))))) :
    ¬ Integrable (B 0) P := by sorry
