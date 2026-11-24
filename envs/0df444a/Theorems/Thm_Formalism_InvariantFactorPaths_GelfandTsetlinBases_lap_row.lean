-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_lap_row
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.lap_row
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:39:49.174687+00:00
-- url     : https://prove2.me/theorems/dacb04fc-db35-4e42-b672-761b9739e312
-- title:
--   Gelfand Tsetlin Bases: lap row
-- statement:
--   The Gelfand Tsetlin Bases construction uses the lap row property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/ActFormContract.lean#L167-L212
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/ActFormContract.lean#L167-L212

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ActFormContract
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
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
variable {R : Type*} [CommRing R] {n : ℕ}

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.lap_row (m : Matrix (Fin n) (Fin n) R) (I' J : Finset (Fin n)) (a : Fin n) :
    ∑ b ∈ J, ((sg J b : ℤ) : R) * minorF m I' (J.erase b) * m a b =
      if a ∈ I' then 0 else ((sg (insert a I') a : ℤ) : R) * minorF m (insert a I') J := by sorry
