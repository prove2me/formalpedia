-- Prove2me | Theorems.Thm_Auto_aux_multilinear_input_deformations
-- name    : Auto.aux_multilinear_input_deformations
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:06:35.667557+00:00
-- url     : https://prove2.me/theorems/d7dc6648-401f-554c-ac03-67bbb1c27999
-- title:
--   Auto: aux multilinear input deformations
-- statement:
--   Packages the usual finite-range input deformations for all but one input of a
--   multilinear interpolation argument.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/MultilinearInterpolation.lean#L7436-L7487
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/MultilinearInterpolation.lean#L7436-L7487

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

theorem Auto.aux_multilinear_input_deformations
    {m : ℕ} {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {p₀ p₁ p : Fin (m + 1) → ENNReal} {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 1)
    (hp₀ : ∀ i, 1 ≤ p₀ i) (hp₁ : ∀ i, 1 ≤ p₁ i) (hp : ∀ i, 1 ≤ p i)
    (hp_top : ∀ i, p i ≠ ∞)
    (hint : ∀ i, (p i)⁻¹ = ENNReal.ofReal (1 - θ) * (p₀ i)⁻¹ +
      ENNReal.ofReal θ * (p₁ i)⁻¹)
    (g : Fin m → SimpleFunc X ℂ)
    (hg : ∀ i, Integrable (g i : X → ℂ) μ)
    (hgnorm : ∀ i, eLpNorm (g i : X → ℂ) (p i.succ) μ ≤ 1) :
    ∃ D : ℂ → Fin m → SimpleFunc X ℂ,
      (∀ i, D (θ : ℂ) i = g i) ∧
      (∀ (z : verticalClosedStrip 0 1) i, Integrable (D z i : X → ℂ) μ) ∧
      (∀ (t : ℝ) i,
        eLpNorm (D ((t : ℂ) * Complex.I) i : X → ℂ) (p₀ i.succ) μ ≤ 1) ∧
      (∀ (t : ℝ) i,
        eLpNorm (D (1 + (t : ℂ) * Complex.I) i : X → ℂ) (p₁ i.succ) μ ≤ 1) := by sorry
