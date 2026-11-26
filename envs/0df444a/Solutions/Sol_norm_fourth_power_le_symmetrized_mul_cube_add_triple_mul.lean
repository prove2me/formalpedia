-- Prove2me | solution 1 for norm_fourth_power_le_symmetrized_mul_cube_add_triple_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:35:23.798591+00:00
-- url     : https://prove2.me/submissions/18f37220-dada-4a9a-ac3d-096d2fc4f834

import Definitions.Def_Operator_Crouzeix_AuxOperator
import Definitions.Def_Operator_SpectralSet_Normal
import Definitions.Def_Operator_Crouzeix_Palencia
import Theorems.Thm_mul_adjoint_fourth_power_eq_symmetrized_sub_triple
import Theorems.Thm_mem_numericalRange
attribute [local simp] mem_numericalRange



set_option autoImplicit false
open scoped InnerProductSpace
theorem _root_.solution
    {B : Type*} [NonUnitalNormedRing B] [StarRing B] [CStarRing B]
    (F G : B) :
    ‖F‖ ^ 4 ≤
      ‖F + star G‖ * ‖F‖ ^ 3 + ‖F * G * F‖ * ‖F‖ := by
  have hidentity := mul_adjoint_fourth_power_eq_symmetrized_sub_triple F G
  have hfour : ‖F‖ ^ 4 = ‖F * star F * F * star F‖ := by
    rw [show F * star F * F * star F =
        (F * star F) * star (F * star F) by
      simp only [star_mul, star_star]
      noncomm_ring]
    rw [CStarRing.norm_self_mul_star, CStarRing.norm_self_mul_star]
    ring
  have hfirst :
      ‖F * star (F + star G) * F * star F‖ ≤
        (‖F‖ * ‖star (F + star G)‖ * ‖F‖) * ‖star F‖ := by
    calc
      _ ≤ ‖F * star (F + star G) * F‖ * ‖star F‖ := norm_mul_le _ _
      _ ≤ (‖F * star (F + star G)‖ * ‖F‖) * ‖star F‖ :=
        mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
      _ ≤ ((‖F‖ * ‖star (F + star G)‖) * ‖F‖) * ‖star F‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
          (norm_nonneg _)
  calc
    ‖F‖ ^ 4 = ‖F * star F * F * star F‖ := hfour
    _ = ‖F * star (F + star G) * F * star F - F * G * F * star F‖ :=
      congrArg norm hidentity
    _ ≤ ‖F * star (F + star G) * F * star F‖ +
        ‖F * G * F * star F‖ := norm_sub_le _ _
    _ ≤ (‖F‖ * ‖star (F + star G)‖ * ‖F‖) * ‖star F‖ +
        ‖F * G * F‖ * ‖star F‖ :=
      add_le_add hfirst (norm_mul_le _ _)
    _ = ‖F + star G‖ * ‖F‖ ^ 3 + ‖F * G * F‖ * ‖F‖ := by
      rw [norm_star, norm_star]
      ring
