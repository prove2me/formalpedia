-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_LowHighPartSplit_lowerUnipotent_symm_apply
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.LowHighPartSplit.lowerUnipotent_symm_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:56:51.255092+00:00
-- url     : https://prove2.me/theorems/98733860-60a6-4545-95d5-cafeb81f86fe
-- title:
--   Low High Part Split: lower Unipotent symm apply
-- statement:
--   The Low High Part Split construction uses the lower Unipotent symm apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/FactSplit.lean#L26-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/FactSplit.lean#L26-L28

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_CorA3primeB
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_IndexWeightsDominance
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_FactSplit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.LowHighPartSplit
variable {n : ℕ}

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.LowHighPartSplit.lowerUnipotent_symm_apply (i : ℕ) (e : ℕ × Fin n →₀ ℕ) (j : ℕ) (a : Fin n) :
    lowP i e (j, a) = if j < i then e (j, a) else 0 := by sorry
