-- Prove2me | Theorems.Thm_Formalism_DivisionValues_idxChange_act_Dg_alg
-- name    : Formalism.DivisionValues.idxChange_act_Dg_alg
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T00:05:39.501849+00:00
-- url     : https://prove2.me/theorems/820c50e5-1a8c-4fe0-8b17-1a304bab9891
-- title:
--   Division Values: idx Change act Dg alg
-- statement:
--   The Division Values construction uses the idx Change act Dg alg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/IdxChange.lean#L283-L289
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/IdxChange.lean#L283-L289

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

theorem Formalism.DivisionValues.idxChange_act_Dg_alg (e : Fin d → Fin d → K) (i : Fin d) (a : R) :
    idxChangeAct e (idxChangeDg i (algebraMap R K a)) = Function.update e i (a • e i) := by sorry
