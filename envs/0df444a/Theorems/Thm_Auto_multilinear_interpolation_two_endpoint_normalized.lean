-- Prove2me | Theorems.Thm_Auto_multilinear_interpolation_two_endpoint_normalized
-- name    : Auto.multilinear_interpolation_two_endpoint_normalized
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:53:43.538294+00:00
-- url     : https://prove2.me/theorems/3d1e2eb2-680a-4ffe-b094-d5de96c0a1f0
-- title:
--   Auto: multilinear interpolation two endpoint normalized
-- statement:
--   The normalized two-endpoint complex interpolation theorem for a complex multilinear
--   map on integrable simple functions.  Its hypotheses are only the endpoint bounds and the
--   basic measurability and scalar-pairing integrability conditions; analyticity and growth of the
--   standard finite-range deformations follow from multilinearity.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/MultilinearInterpolation.lean#L7901-L8003
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/MultilinearInterpolation.lean#L7901-L8003

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

theorem Auto.multilinear_interpolation_two_endpoint_normalized
    {m : ℕ} {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} [SigmaFinite ν]
    (B : MultilinearMap ℂ (fun _ : Fin (m + 1) ↦ SimpleFunc X ℂ) (Y → ℂ))
    {p₀ p₁ p : Fin (m + 1) → ENNReal} {q : ENNReal} {θ M₀ M₁ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 1)
    (hp₀ : ∀ i, 1 ≤ p₀ i) (hp₁ : ∀ i, 1 ≤ p₁ i) (hp : ∀ i, 1 ≤ p i)
    (hp_top : ∀ i, p i ≠ ∞)
    (hint : ∀ i, (p i)⁻¹ = ENNReal.ofReal (1 - θ) * (p₀ i)⁻¹ +
      ENNReal.ofReal θ * (p₁ i)⁻¹)
    (hq : 1 ≤ q) (hM₀ : 0 < M₀) (hM₁ : 0 < M₁)
    (hB_measurable : ∀ u : Fin (m + 1) → SimpleFunc X ℂ,
      (∀ i, Integrable (u i : X → ℂ) μ) → Measurable (B u))
    (hB_pair_integrable : ∀ (u : Fin (m + 1) → SimpleFunc X ℂ)
      (h : SimpleFunc Y ℂ),
      (∀ i, Integrable (u i : X → ℂ) μ) → Integrable (h : Y → ℂ) ν →
        Integrable (fun y ↦ B u y * h y) ν)
    (hB_bound₀ : ∀ u : Fin (m + 1) → SimpleFunc X ℂ,
      (∀ i, Integrable (u i : X → ℂ) μ) →
        eLpNorm (B u) q ν ≤ ENNReal.ofReal M₀ * ∏ i,
          eLpNorm (u i : X → ℂ) (p₀ i) μ)
    (hB_bound₁ : ∀ u : Fin (m + 1) → SimpleFunc X ℂ,
      (∀ i, Integrable (u i : X → ℂ) μ) →
        eLpNorm (B u) q ν ≤ ENNReal.ofReal M₁ * ∏ i,
          eLpNorm (u i : X → ℂ) (p₁ i) μ)
    (g : Fin (m + 1) → SimpleFunc X ℂ)
    (hg : ∀ i, Integrable (g i : X → ℂ) μ)
    (hgnorm : ∀ i : Fin m, eLpNorm (g i.succ : X → ℂ) (p i.succ) μ ≤ 1) :
    MemLp (B g) q ν ∧
      eLpNorm (B g) q ν ≤
        ENNReal.ofReal (Real.rpow M₀ (1 - θ) * Real.rpow M₁ θ) *
          eLpNorm (g 0 : X → ℂ) (p 0) μ := by sorry
