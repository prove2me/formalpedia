-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_LowHighPartSplit_mem_polB
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.LowHighPartSplit.mem_polB
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:35:09.476272+00:00
-- url     : https://prove2.me/theorems/27227d87-bd99-4480-b1d0-bbb7a5e400b2
-- title:
--   Low High Part Split: mem pol B
-- statement:
--   The Low High Part Split construction uses the mem pol B property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/FactSplit.lean#L50-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/FactSplit.lean#L50-L60

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

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.LowHighPartSplit.mem_polB {R : Type*} [CommRing R] {N : ℕ} {B : ℕ → ℕ} {f : MvPolynomial (ℕ × Fin n) R} :
    f ∈ polB R n N B ↔ ∀ e ∈ f.support, ∀ j, ∑ a, e (j, a) = if j < N then B j else 0 := by sorry
