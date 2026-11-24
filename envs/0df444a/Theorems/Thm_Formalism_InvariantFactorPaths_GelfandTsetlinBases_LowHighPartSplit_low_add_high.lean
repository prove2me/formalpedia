-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_LowHighPartSplit_low_add_high
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.LowHighPartSplit.low_add_high
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:35:09.370889+00:00
-- url     : https://prove2.me/theorems/2cf44bbb-abb3-4bc9-a07a-9e3b50d6ae1a
-- title:
--   Low High Part Split: low add high
-- statement:
--   The Low High Part Split construction uses the low add high property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/FactSplit.lean#L21-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/FactSplit.lean#L21-L24

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

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.LowHighPartSplit.low_add_high (i : ℕ) (e : ℕ × Fin n →₀ ℕ) : lowP i e + highP i e = e := by sorry
