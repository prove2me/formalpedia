-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_integral_radial_inverse_cube
-- name    : Formalism.HermitianLatticeCounting.P.integral_radial_inverse_cube
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:37:11.962818+00:00
-- url     : https://prove2.me/theorems/54368ade-8926-4018-9c4c-b125f040e034
-- title:
--   P: integral radial inverse cube
-- statement:
--   The P construction uses the integral radial inverse cube property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SchurAverage.lean#L458-L487
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SchurAverage.lean#L458-L487

import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SchurAverage
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open InnerProductSpace
open MeasureTheory Set

theorem Formalism.HermitianLatticeCounting.P.integral_radial_inverse_cube (H : ℝ) (hH : 0 < H) :
    IntegrableOn (fun y : ℝ => y * ((max 1 (y / H)) ^ 3)⁻¹) (Ioi 0) ∧
      ∫ y in Ioi (0:ℝ), y * ((max 1 (y / H)) ^ 3)⁻¹ = 3 * H ^ 2 / 2 := by sorry
