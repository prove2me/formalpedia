-- Prove2me | Theorems.Thm_Formalism_DivisionValues_idxChange_transvection_conj
-- name    : Formalism.DivisionValues.idxChange_transvection_conj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:31:48.239026+00:00
-- url     : https://prove2.me/theorems/41183db7-1282-478a-8da2-be1d5c3aeae3
-- title:
--   Division Values: idx Change transvection conj
-- statement:
--   The Division Values construction uses the idx Change transvection conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/IdxChange.lean#L601-L621
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/IdxChange.lean#L601-L621

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

theorem Formalism.DivisionValues.idxChange_transvection_conj {i j : Fin d} (hij : i ≠ j) {c : K} (hc : c ≠ 0) :
    Matrix.transvection i j c =
      idxChangeDg i c * Matrix.transvection i j (1 : K) * idxChangeDg i c⁻¹ := by sorry
