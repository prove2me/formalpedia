-- Prove2me | Theorems.Thm_Formalism_L2_Th1_B_dz_cube
-- name    : Formalism.L2.Th1.B.dz_cube
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:21:49.51704+00:00
-- url     : https://prove2.me/theorems/9a0d500a-9cc9-4620-b25d-c5dd8d9e7ff3
-- title:
--   B: dz cube
-- statement:
--   The B construction uses the dz cube property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/WeierstrassReducedEquations.lean#L48-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/WeierstrassReducedEquations.lean#L48-L50

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_WeierstrassReducedEquations
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B
open PowerSeries
variable {K : Type} [Field K] [CharZero K]

theorem Formalism.L2.Th1.B.dz_cube (f : PowerSeries K) : dz (f ^ 3) = 3 * f ^ 2 * dz f := by sorry
