-- Prove2me | solution 1 for vonNeumann_inequality_of_exists_unitary_power_dilation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:44:54.748949+00:00
-- url     : https://prove2.me/submissions/50c578b0-707f-43ce-ad8f-4c279575b118

import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Definitions.Def_Operator_Dilation_Schaeffer
import Definitions.Def_Operator_SpectralSet_Basic
import Definitions.Def_Operator_Crouzeix_VonNeumann
import Theorems.Thm_norm_aeval_le_polynomialSupNorm_closedBall_of_mem_unitary
import Theorems.Thm_norm_aeval_le_norm_aeval_of_dilation

set_option autoImplicit false
open Polynomial ContinuousLinearMap
open scoped InnerProductSpace
universe u
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
theorem _root_.solution (T : E →L[ℂ] E)
    (hdil : ∃ (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (_ : CompleteSpace H) (V : E →L[ℂ] H) (U : H →L[ℂ] H),
      (∀ x y : E, ⟪V x, V y⟫_ℂ = ⟪x, y⟫_ℂ) ∧
      U ∈ unitary (H →L[ℂ] H) ∧
      (∀ (n : ℕ) (x : E), adjoint V ((U ^ n) (V x)) = (T ^ n) x))
    (p : ℂ[X]) :
    ‖aeval T p‖ ≤ polynomialSupNorm p (Metric.closedBall (0 : ℂ) 1) := by
  obtain ⟨H, _, _, _, V, U, hV, hU, hpow⟩ := hdil
  exact (norm_aeval_le_norm_aeval_of_dilation T V U hV hpow p).trans
    (norm_aeval_le_polynomialSupNorm_closedBall_of_mem_unitary hU p)
