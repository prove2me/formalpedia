-- Prove2me | Theorems.Thm_Auto_riesz_thorin
-- name    : Auto.riesz_thorin
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:06:28.367482+00:00
-- url     : https://prove2.me/theorems/d5592174-1299-5a83-bd39-052f24a8de61
-- title:
--   Auto: riesz thorin
-- statement:
--   **Riesz--Thorin interpolation**, obtained from `stein_interpolation_constant_bounds` by
--   taking the analytic family to be constant.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/MultilinearInterpolation.lean#L7310-L7361
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/MultilinearInterpolation.lean#L7310-L7361

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

theorem Auto.riesz_thorin
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} [SigmaFinite ν]
    {p₀ p₁ p q₀ q₁ q : ENNReal} {θ M₀ M₁ : ℝ}
    (T : SimpleFunc X ℂ → Y → ℂ)
    (hp₀ : 1 ≤ p₀) (hp₁ : 1 ≤ p₁) (hq₀ : 1 ≤ q₀) (hq₁ : 1 ≤ q₁)
    (hθ : θ ∈ Set.Ioo 0 1)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹)
    (hq : q⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹ + ENNReal.ofReal θ * q₁⁻¹)
    (hT_add : ∀ (f g : SimpleFunc X ℂ),
      Integrable f μ → Integrable g μ → T (f + g) = T f + T g)
    (hT_smul : ∀ (c : ℂ) (f : SimpleFunc X ℂ),
      Integrable f μ → T (c • f) = c • T f)
    (hT_measurable : ∀ (f : SimpleFunc X ℂ),
      Integrable f μ → Measurable (T f))
    (hM₀ : 0 < M₀) (hM₁ : 0 < M₁)
    (hbound₀ : ∀ (f : SimpleFunc X ℂ), Integrable f μ →
      eLpNorm (T f) q₀ ν ≤ ENNReal.ofReal M₀ * eLpNorm (f : X → ℂ) p₀ μ)
    (hbound₁ : ∀ (f : SimpleFunc X ℂ), Integrable f μ →
      eLpNorm (T f) q₁ ν ≤ ENNReal.ofReal M₁ * eLpNorm (f : X → ℂ) p₁ μ) :
    ∀ f : SimpleFunc X ℂ, Integrable f μ →
      MemLp (T f) q ν ∧
      eLpNorm (T f) q ν ≤
        ENNReal.ofReal (Real.rpow M₀ (1 - θ) * Real.rpow M₁ θ) *
          eLpNorm (f : X → ℂ) p μ := by sorry
