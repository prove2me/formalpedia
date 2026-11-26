-- Prove2me | solution 1 for norm_eval_le_polynomialSupNorm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:34:08.202703+00:00
-- url     : https://prove2.me/submissions/ec4955ec-c5f3-4bcc-9761-8cf5c99c6850

import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Definitions.Def_Operator_Dilation_Schaeffer
import Definitions.Def_Operator_SpectralSet_Basic
import Definitions.Def_Operator_Crouzeix_VonNeumann

set_option autoImplicit false
open Polynomial ContinuousLinearMap
open scoped InnerProductSpace
universe u
theorem _root_.solution (p : ℂ[X]) {X : Set ℂ}
    (hX : BddAbove ((fun z => ‖p.eval z‖) '' X)) {z : ℂ} (hz : z ∈ X) :
    ‖p.eval z‖ ≤ polynomialSupNorm p X := by
  obtain ⟨M, hM⟩ := hX
  unfold polynomialSupNorm
  refine le_ciSup₂ (f := fun z (_ : z ∈ X) => ‖p.eval z‖) ⟨M, ?_⟩ z hz
  rintro y hy
  rw [Set.mem_iUnion] at hy
  obtain ⟨w, hw⟩ := hy
  rw [Set.mem_range] at hw
  obtain ⟨hwX, rfl⟩ := hw
  exact hM ⟨w, hwX, rfl⟩
