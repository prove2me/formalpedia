-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_integral_inverse_cube_plateau
-- name    : Formalism.HermitianLatticeCounting.P.integral_inverse_cube_plateau
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:37:12.352802+00:00
-- url     : https://prove2.me/theorems/5813057c-cf6c-4f48-90c7-dc28f8c204d2
-- title:
--   P: integral inverse cube plateau
-- statement:
--   The P construction uses the integral inverse cube plateau property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SchurAverage.lean#L490-L506
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SchurAverage.lean#L490-L506

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
open MeasureTheory

theorem Formalism.HermitianLatticeCounting.P.integral_inverse_cube_plateau (H : ℝ) (hH : 0 < H) :
    Integrable (fun z : ℂ => ((max 1 (‖z‖ / H)) ^ 3)⁻¹) ∧
      ∫ z : ℂ, ((max 1 (‖z‖ / H)) ^ 3)⁻¹ = 3 * Real.pi * H ^ 2 := by sorry
