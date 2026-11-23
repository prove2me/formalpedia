-- Prove2me | Theorems.Thm_Formalism_DivisionValues_indexChangeAction_transvection
-- name    : Formalism.DivisionValues.indexChangeAction_transvection
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:31:46.72796+00:00
-- url     : https://prove2.me/theorems/df297afd-14c0-401a-a72a-26120e4cea78
-- title:
--   Division Values: index Change Action transvection
-- statement:
--   The Division Values construction uses the index Change Action transvection property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/IdxChange.lean#L556-L564
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/IdxChange.lean#L556-L564

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module IsDedekindDomain Formalism.HermitianLatticesTheory
open scoped Matrix nonZeroDivisors
noncomputable section
open Formalism Formalism.DivisionValues
variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] {d : ℕ}

theorem Formalism.DivisionValues.indexChangeAction_transvection (e : Fin d → Fin d → K) {i j : Fin d} (hij : i ≠ j) :
    idxChangeAct e (Matrix.transvection i j (1 : K)) = Function.update e j (e j + e i) := by sorry
