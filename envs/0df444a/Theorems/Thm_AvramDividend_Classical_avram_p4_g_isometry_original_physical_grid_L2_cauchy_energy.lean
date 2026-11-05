-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_original_physical_grid_L2_cauchy_energy
-- name    : AvramDividend.Classical.avram_p4_g_isometry_original_physical_grid_L2_cauchy_energy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T21:59:05.334595+00:00
-- url     : https://prove2.me/theorems/fda008bf-f527-4e6d-ace6-334679d2cfc9
-- title:
--   Original intrinsic finite-grid L2 Cauchy energy criterion for predictable approximants
-- statement:
--   For predictable bounded finite-grid coefficient approximations on the same original Lévy sample space, a Cauchy modulus for their deterministic Lévy-intensity L2 energy implies exactly the same Cauchy modulus for the physical compensated intrinsic jump sums in L2(P). Source-exact physical ordered pair intensity and future-sigma independence remain explicit premises. The conclusion is an L2 energy Cauchy criterion and does not yet construct a complete stochastic integral.
-- source:
--   Proved/public physical original finite-grid L2 distance 6b7bb799 and an explicit predictable coefficient energy Cauchy hypothesis. No abstract Poisson substitution or optional stopping.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_original_finite_grid_predictable_L2_distance

open MeasureTheory Set AvramDividend.Classical ProbabilityTheory
open scoped NNReal ENNReal Nat BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p4_g_isometry_original_physical_grid_L2_cauchy_energy
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (grid : ℕ → ℝ≥0) (hGrid : ∀ i, grid i ≤ grid (i + 1))
    (ε : ℝ) (hε : 0 < ε) (B : ℕ → Set ℝ)
    (hB : ∀ i, MeasurableSet (B i))
    (hBand : ∀ i, B i ⊆ Ioo (-1 : ℝ) (-ε))
    (hν : ∀ i, X.ν (B i) < ⊤)
    (N : ℕ → Ω → ℝ≥0∞)
    (hActual : ∀ i, N i = fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (grid i) (grid (i + 1)) ×ˢ B i))
    (r : ℕ → ℝ)
    (hRate : ∀ i, r i =
      (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) * X.ν (B i)).toReal)
    (H : ℕ → ℕ → Ω → ℝ)
    (hH : ∀ j i, StronglyMeasurable[𝓕 (grid i)] (H j i))
    (hHInf : ∀ j i, MemLp (H j i) ⊤ P)
    (hCountEndpoint : ∀ i, StronglyMeasurable[𝓕 (grid (i + 1))]
      (fun ω => (N i ω).toReal))
    (K : ℕ → Ω → ℝ≥0∞)
    (hKMeas : ∀ i, Measurable (K i))
    (hPhysicalPair : ∀ i ω,
      (N i ω).toReal * ((N i ω).toReal - 1) = 2 * (K i ω).toReal)
    (hPairMean : ∀ i,
      (∫⁻ ω, K i ω ∂P) = ENNReal.ofReal
        (((((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
          X.ν (B i)).toReal) ^ 2 / 2))
    (mFuture : ℕ → MeasurableSpace Ω)
    (hFuture : ∀ i, mFuture i ≤ mΩ)
    (hSqMeas : ∀ i, StronglyMeasurable[mFuture i]
      (fun ω => ((N i ω).toReal - r i) ^ 2))
    (hIndependent : ∀ i, Indep (mFuture i) (𝓕 (grid i)) P)
    (n : ℕ)
    (hEnergy : ∀ δ : ℝ, 0 < δ →
      ∃ M : ℕ, ∀ j k : ℕ, M ≤ j → M ≤ k →
      (∑ i ∈ Finset.range n, r i *
        ∫ ω, (H j i ω - H k i ω) ^ 2 ∂P) < δ) :
    ∀ δ : ℝ, 0 < δ →
      ∃ M : ℕ, ∀ j k : ℕ, M ≤ j → M ≤ k →
      (∫ ω, ((∑ i ∈ Finset.range n,
        H j i ω * ((N i ω).toReal - r i)) -
        (∑ i ∈ Finset.range n,
        H k i ω * ((N i ω).toReal - r i))) ^ 2 ∂P) < δ := by sorry
