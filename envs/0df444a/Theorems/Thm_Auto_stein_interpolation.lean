-- Prove2me | Theorems.Thm_Auto_stein_interpolation
-- name    : Auto.stein_interpolation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:53:30.747196+00:00
-- url     : https://prove2.me/theorems/e3eb3815-65c6-5dbb-ab0c-7fcb1d66819f
-- title:
--   Auto: stein interpolation
-- statement:
--   **Stein's interpolation theorem** for an analytic family of raw operators.
--
--   The common domain is the integrable-simple-function core: for a simple function,
--   `Integrable f μ` is equivalent to finite measure support. Analyticity is the source theorem's
--   weak scalar-pairing analyticity, and the conclusion has the exact Hirschman
--   harmonic-measure constant.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/MultilinearInterpolation.lean#L6885-L7254
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/MultilinearInterpolation.lean#L6885-L7254

module
public import Mathlib.Analysis.Complex.Hadamard
public import Mathlib.Analysis.Complex.CanonicalDecomposition
public import Mathlib.Analysis.Complex.JensenFormula
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
public import Mathlib.LinearAlgebra.Multilinear.Curry
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Analysis.Normed.Module.Multilinear.Basic
public import Definitions.Def_LeanNct_Auto_MultilinearInterpolation
set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Complex.HadamardThreeLines Real Filter Topology ENNReal Asymptotics Set Metric
  MeromorphicOn
open scoped BigOperators
open Auto

theorem Auto.stein_interpolation
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} [SigmaFinite ν]
    {p₀ p₁ p q₀ q₁ q : ENNReal} {θ : ℝ} {M₀ M₁ : ℝ → ℝ}
    (T : ℂ → SimpleFunc X ℂ → Y → ℂ)
    (hp₀ : 1 ≤ p₀) (hp₁ : 1 ≤ p₁) (hq₀ : 1 ≤ q₀) (hq₁ : 1 ≤ q₁)
    (hθ : θ ∈ Set.Ioo 0 1)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹)
    (hq : q⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹ + ENNReal.ofReal θ * q₁⁻¹)
    (hT_add : ∀ (z : verticalClosedStrip 0 1) (f g : SimpleFunc X ℂ),
      Integrable f μ → Integrable g μ → T z (f + g) = T z f + T z g)
    (hT_smul : ∀ (z : verticalClosedStrip 0 1) (c : ℂ) (f : SimpleFunc X ℂ),
      Integrable f μ → T z (c • f) = c • T z f)
    (hT_measurable : ∀ (z : verticalClosedStrip 0 1) (f : SimpleFunc X ℂ),
      Integrable f μ → Measurable (T z f))
    (hpair_integrable : ∀ (z : verticalClosedStrip 0 1)
      (f : SimpleFunc X ℂ) (g : SimpleFunc Y ℂ),
      Integrable f μ → Integrable g ν → Integrable (fun y ↦ T z f y * g y) ν)
    (hanalytic : ∀ (f : SimpleFunc X ℂ) (g : SimpleFunc Y ℂ),
      Integrable f μ → Integrable g ν →
      DiffContOnCl ℂ (fun z ↦ ∫ y, T z f y * g y ∂ν) (verticalStrip 0 1))
    (hfamily_growth : ∃ a : ℝ, a < Real.pi ∧
      ∀ (f : SimpleFunc X ℂ) (g : SimpleFunc Y ℂ),
        Integrable f μ → Integrable g ν →
        ∃ C : ℝ, ∀ z : verticalClosedStrip 0 1,
          ‖∫ y, T z f y * g y ∂ν‖ ≤ exp (C * exp (a * |(z : ℂ).im|)))
    (hM_measurable : Measurable M₀ ∧ Measurable M₁)
    (hM_pos : ∀ t : ℝ, 0 < M₀ t ∧ 0 < M₁ t)
    (hM_growth : ∃ b A : ℝ, b < Real.pi ∧ ∀ t : ℝ,
      |log (M₀ t)| ≤ A * exp (b * |t|) ∧ |log (M₁ t)| ≤ A * exp (b * |t|))
    (hbound₀ : ∀ (t : ℝ) (f : SimpleFunc X ℂ), Integrable f μ →
      eLpNorm (T ((t : ℂ) * Complex.I) f) q₀ ν ≤
        ENNReal.ofReal (M₀ t) * eLpNorm (f : X → ℂ) p₀ μ)
    (hbound₁ : ∀ (t : ℝ) (f : SimpleFunc X ℂ), Integrable f μ →
      eLpNorm (T (1 + (t : ℂ) * Complex.I) f) q₁ ν ≤
        ENNReal.ofReal (M₁ t) * eLpNorm (f : X → ℂ) p₁ μ) :
    ∀ f : SimpleFunc X ℂ, Integrable f μ →
      MemLp (T (θ : ℂ) f) q ν ∧
      eLpNorm (T (θ : ℂ) f) q ν ≤
        ENNReal.ofReal
          (exp
            ((sin (Real.pi * θ) / 2) *
              ∫ t : ℝ,
                log (M₀ t) / (cosh (Real.pi * t) - cos (Real.pi * θ)) +
                  log (M₁ t) / (cosh (Real.pi * t) + cos (Real.pi * θ)))) *
          eLpNorm (f : X → ℂ) p μ := by sorry
