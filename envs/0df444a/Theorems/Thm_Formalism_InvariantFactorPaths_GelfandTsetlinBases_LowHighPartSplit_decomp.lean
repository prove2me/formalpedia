-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_LowHighPartSplit_decomp
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.LowHighPartSplit.decomp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:57:09.763269+00:00
-- url     : https://prove2.me/theorems/344cd9a3-400f-43f7-a661-286d1b876c45
-- title:
--   Low High Part Split: decomp
-- statement:
--   The Low High Part Split construction uses the decomp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/FactSplit.lean#L66-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/FactSplit.lean#L66-L75

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

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.LowHighPartSplit.decomp {k : Type*} [CommRing k] (i : ℕ) (G : MvPolynomial (ℕ × Fin n) k) :
    G = ∑ β ∈ G.support.image (highP i), Gc i G β * monomial β 1 := by sorry
