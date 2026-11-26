-- Prove2me | solution 1 for norm_aeval_le_norm_aeval_of_dilation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:43:57.229592+00:00
-- url     : https://prove2.me/submissions/f7d0ed1f-97ae-4394-9aa2-a0a74db5856b

import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Definitions.Def_Operator_Dilation_Schaeffer
import Definitions.Def_Operator_SpectralSet_Basic
import Definitions.Def_Operator_Crouzeix_VonNeumann
import Theorems.Thm_adjoint_aeval_apply_of_forall_pow

set_option autoImplicit false
open Polynomial ContinuousLinearMap
open scoped InnerProductSpace
universe u
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
theorem _root_.solution (T : E →L[ℂ] E) (V : E →L[ℂ] H) (U : H →L[ℂ] H)
    (hV : ∀ x y : E, ⟪V x, V y⟫_ℂ = ⟪x, y⟫_ℂ)
    (hpow : ∀ (n : ℕ) (x : E), adjoint V ((U ^ n) (V x)) = (T ^ n) x) (p : ℂ[X]) :
    ‖aeval T p‖ ≤ ‖aeval U p‖ := by
  have hVnorm : ∀ x, ‖V x‖ = ‖x‖ := (LinearMap.norm_map_iff_inner_map_map V).mpr hV
  have hV1 : ‖V‖ ≤ 1 := V.opNorm_le_bound zero_le_one fun x => by rw [hVnorm x, one_mul]
  refine (aeval T p).opNorm_le_bound (norm_nonneg _) fun x => ?_
  rw [← adjoint_aeval_apply_of_forall_pow T V U hpow p x]
  calc ‖adjoint V ((aeval U p) (V x))‖
      ≤ ‖adjoint V‖ * ‖(aeval U p) (V x)‖ := le_opNorm _ _
    _ ≤ ‖adjoint V‖ * (‖aeval U p‖ * ‖V x‖) := by gcongr; exact le_opNorm _ _
    _ = ‖V‖ * ‖aeval U p‖ * ‖x‖ := by rw [adjoint.norm_map, hVnorm]; ring
    _ ≤ 1 * ‖aeval U p‖ * ‖x‖ := by gcongr
    _ = ‖aeval U p‖ * ‖x‖ := by ring
