-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_det_rows_expand
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.det_rows_expand
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:39:46.095801+00:00
-- url     : https://prove2.me/theorems/7852c4b6-acba-4d1b-ae87-bceb5328e356
-- title:
--   Gelfand Tsetlin Bases: det rows expand
-- statement:
--   The Gelfand Tsetlin Bases construction uses the det rows expand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/ActFormContract.lean#L147-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/ActFormContract.lean#L147-L165

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

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.det_rows_expand {d : ℕ} (m : Matrix (Fin n) (Fin n) R) (r : Fin (d + 1) → Fin n) (i : Fin (d + 1))
    {I' J : Finset (Fin n)} (hJ : J.card = d + 1) (hI' : I'.card = d)
    (hr : (fun x => r (i.succAbove x)) = I'.orderEmbOfFin hI') :
    (-1 : R) ^ (d + (i : ℕ)) * (m.submatrix r (J.orderEmbOfFin hJ)).det =
      ∑ b ∈ J, ((sg J b : ℤ) : R) * minorF m I' (J.erase b) * m (r i) b := by sorry
