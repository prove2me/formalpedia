-- Prove2me | Theorems.Thm_Formalism_L2_Th1_B_Add1_partialDeriv_inVar_of_ne
-- name    : Formalism.L2.Th1.B.Add1.partialDeriv_inVar_of_ne
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:47:44.886873+00:00
-- url     : https://prove2.me/theorems/4b33a2e1-744a-4ea0-b4d1-3410149788cf
-- title:
--   Add1: partial Deriv in Var of ne
-- statement:
--   The Add1 construction uses the partial Deriv in Var of ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/RestrictSecondZeroInVarOne.lean#L72-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/RestrictSecondZeroInVarOne.lean#L72-L75

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementA
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_RestrictSecondZeroInVarOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.Add1
open Formalism.InvariantFactorPaths.G7 (at1)
variable {K : Type} [Field K] [CharZero K]

theorem Formalism.L2.Th1.B.Add1.partialDeriv_inVar_of_ne {x y : Fin 2} (h : y ≠ x) (f : PowerSeries K) : pd x (at1 y f) = 0 := by sorry
