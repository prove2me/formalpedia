-- Prove2me | solution 1 for exists_contDiffAt_leftInverse_of_injective_fderiv
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-07T17:25:06.151013+00:00
-- url     : https://prove2.me/submissions/7639ed51-8bd1-407d-ac66-83ed10d7fdf9

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.LinearAlgebra.Basis.VectorSpace

open scoped ContDiff Topology

/-- A smooth map whose differential at `p` is injective has a smooth local left inverse
near `e p`: there is `g`, smooth at `e p`, with `g (e q) = q` for all `q` near `p`. -/
theorem exists_contDiffAt_leftInverse_of_injective_fderiv_aux
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {e : E → F} {p : E} (he : ContDiffAt ℝ ∞ e p)
    (hinj : Function.Injective (fderiv ℝ e p)) :
    ∃ g : F → E, ContDiffAt ℝ ∞ g (e p) ∧ ∀ᶠ q in 𝓝 p, g (e q) = q := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨L, hL⟩ := ((fderiv ℝ e p : E →L[ℝ] F) : E →ₗ[ℝ] F).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.2 hinj)
  let Lc : F →L[ℝ] E := LinearMap.toContinuousLinearMap L
  let f : E → E := fun q => Lc (e q)
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  have hcomp : Lc.comp (fderiv ℝ e p) = ((ContinuousLinearEquiv.refl ℝ E : E ≃L[ℝ] E) : E →L[ℝ] E) := by
    ext v
    have := congrArg (fun φ : E →ₗ[ℝ] E => φ v) hL
    simpa [Lc] using this
  have hfd : HasFDerivAt f ((ContinuousLinearEquiv.refl ℝ E : E ≃L[ℝ] E) : E →L[ℝ] E) p := by
    rw [← hcomp]
    exact Lc.hasFDerivAt.comp p (he.differentiableAt (by simp)).hasFDerivAt
  have hf : ContDiffAt ℝ ∞ f p := Lc.contDiff.contDiffAt.comp p he
  refine ⟨fun y => hf.localInverse hfd hn (Lc y), ?_, ?_⟩
  · exact (hf.to_localInverse hfd hn).comp (e p) Lc.contDiff.contDiffAt
  · exact (hf.hasStrictFDerivAt' hfd hn).eventually_left_inverse

theorem solution
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {e : E → F} {p : E} (he : ContDiffAt ℝ ∞ e p)
    (hinj : Function.Injective (fderiv ℝ e p)) :
    ∃ g : F → E, ContDiffAt ℝ ∞ g (e p) ∧ ∀ᶠ q in 𝓝 p, g (e q) = q :=
  exists_contDiffAt_leftInverse_of_injective_fderiv_aux he hinj
