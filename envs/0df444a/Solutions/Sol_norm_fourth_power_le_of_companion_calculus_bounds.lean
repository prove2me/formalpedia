-- Prove2me | solution 1 for norm_fourth_power_le_of_companion_calculus_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:36:14.615802+00:00
-- url     : https://prove2.me/submissions/55eccb85-22c1-494f-ab0a-a4316df87b43

import Definitions.Def_Operator_Crouzeix_AuxOperator
import Definitions.Def_Operator_SpectralSet_Normal
import Definitions.Def_Operator_Crouzeix_Palencia
import Theorems.Thm_norm_fourth_power_le_symmetrized_mul_cube_add_triple_mul

set_option autoImplicit false
open scoped InnerProductSpace
theorem _root_.solution
    {B : Type*} [NonUnitalNormedRing B] [StarRing B] [CStarRing B]
    (F G : B) {K m : ℝ} (hK : 0 ≤ K) (hm : 0 ≤ m)
    (hsymm : ‖F + star G‖ ≤ 2 * m) (hF : ‖F‖ ≤ K * m)
    (htriple : ‖F * G * F‖ ≤ K * m ^ 3) :
    ‖F‖ ^ 4 ≤ (2 * K ^ 3 + K ^ 2) * m ^ 4 := by
  have hbase := norm_fourth_power_le_symmetrized_mul_cube_add_triple_mul F G
  calc
    ‖F‖ ^ 4 ≤ ‖F + star G‖ * ‖F‖ ^ 3 + ‖F * G * F‖ * ‖F‖ := hbase
    _ ≤ (2 * m) * (K * m) ^ 3 + (K * m ^ 3) * (K * m) := by
      gcongr
    _ = (2 * K ^ 3 + K ^ 2) * m ^ 4 := by ring
