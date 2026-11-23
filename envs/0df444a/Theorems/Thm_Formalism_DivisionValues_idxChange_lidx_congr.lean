-- Prove2me | Theorems.Thm_Formalism_DivisionValues_idxChange_lidx_congr
-- name    : Formalism.DivisionValues.idxChange_lidx_congr
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:49:51.527404+00:00
-- url     : https://prove2.me/theorems/2ba68fac-3fbf-4801-9972-77318ebd7c51
-- title:
--   Division Values: idx Change lidx congr
-- statement:
--   The Division Values construction uses the idx Change lidx congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/IdxChange.lean#L182-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/IdxChange.lean#L182-L188

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

theorem Formalism.DivisionValues.idxChange_lidx_congr (p : Ideal R) [p.IsPrime] {A A' B B' : Submodule R (Fin d → K)}
    (hA : localization₂ p A = localization₂ p A') (hB : localization₂ p B = localization₂ p B') : lidx p A B = lidx p A' B' := by sorry
