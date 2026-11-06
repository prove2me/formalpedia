-- Prove2me | Theorems.Thm_EthierKurtz_martingale_problem_rectangle_step_for_finite_dimensional_distributions
-- name    : EthierKurtz.martingale_problem_rectangle_step_for_finite_dimensional_distributions
-- status  : Open
-- author  : @WillR
-- created : 2026-11-06T02:25:52.776342+00:00
-- url     : https://prove2.me/theorems/cef1f398-a811-45ae-ad89-97b4ca4e1e48
-- title:
--   Rectangular one-step uniqueness for martingale solutions
-- statement:
--   For two solutions of the same martingale problem with the same initial law, suppose their joint laws agree at an ordered past vector. For any measurable rectangle of past values and any later terminal time, the restricted terminal laws agree. This isolates the one-step uniqueness argument used to prove equality of finite-dimensional distributions.
-- source:
--   Source-faithful reduction of parent theorem EthierKurtz.martingale_problem_determines_finite_dimensional_distributions (target e7f29b55-7342-4ff0-afdb-be23ceaf9cb9, revision 0f57fdc08f2032c2ce50bce03cee7ff6234a6681537b0ad40472b73238514671). It isolates the fixed-rectangle weak-forward, resolvent, Laplace uniqueness, and hsep step.

import Mathlib
import Definitions.Def_auto_M04_6e37b463_UniformBoundedFunction
import Definitions.Def_auto_M04_6e37b463_processPast
import Definitions.Def_auto_M04_6e37b463_SolvesMartingaleProblem
open MeasureTheory Filter TopologicalSpace
open scoped ENNReal NNReal Topology
open EthierKurtz

theorem EthierKurtz.martingale_problem_rectangle_step_for_finite_dimensional_distributions
    {E Ω Ω' : Type*} [MeasurableSpace E] [MeasurableSpace Ω]
    [MeasurableSpace Ω'] [MetricSpace E] [BorelSpace E]
    [SeparableSpace E]
    (A A' : Submodule ℝ (UniformBoundedFunction E × UniformBoundedFunction E))
    (hAmeas : ∀ fg ∈ A, Measurable (fg.1 : E → ℝ) ∧ Measurable (fg.2 : E → ℝ))
    (hsub : A' ≤ A)
    (hdiss : ∀ fg ∈ A, ∀ a : ℝ, 0 < a →
      a * ‖fg.1‖ ≤ ‖a • fg.1 - fg.2‖)
    (L : Submodule ℝ (UniformBoundedFunction E))
    (hrange : ∃ a : ℝ, 0 < a ∧
      closure ((fun fg : UniformBoundedFunction E × UniformBoundedFunction E =>
        a • fg.1 - fg.2) '' (A' : Set _)) = (L : Set _) ∧
      closure ((fun fg : UniformBoundedFunction E × UniformBoundedFunction E =>
        fg.1) '' (A' : Set _)) = (L : Set (UniformBoundedFunction E)))
    (hsep : ∀ (ν₁ ν₂ : Measure E), IsProbabilityMeasure ν₁ →
      IsProbabilityMeasure ν₂ →
      (∀ f : L, (∫ x, (f.val : E → ℝ) x ∂ν₁) =
        ∫ x, (f.val : E → ℝ) x ∂ν₂) → ν₁ = ν₂)
    (μ : Measure E) [IsProbabilityMeasure μ]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → E) (hX : SolvesMartingaleProblem A μ P X)
    (Q : Measure Ω') [IsProbabilityMeasure Q]
    (Y : ℝ≥0 → Ω' → E) (hY : SolvesMartingaleProblem A μ Q Y)
    (n : ℕ) (r : Fin n → ℝ≥0) (j : Fin n) (u v : ℝ≥0)
    (hr : ∀ i, r i ≤ u) (hju : r j = u) (huv : u ≤ v)
    (B : Fin n → Set E) (hB : ∀ i, MeasurableSet (B i))
    (hpast : Measure.map (fun ω i => X (r i) ω) P =
      Measure.map (fun ω i => Y (r i) ω) Q) :
    Measure.map (fun ω => X v ω)
        (P.restrict {ω | ∀ i, X (r i) ω ∈ B i}) =
      Measure.map (fun ω => Y v ω)
        (Q.restrict {ω | ∀ i, Y (r i) ω ∈ B i}) := by sorry
