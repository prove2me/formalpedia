-- Prove2me | Theorems.Thm_Formalism_DivisionValues_indexChangeLocal_transvection
-- name    : Formalism.DivisionValues.indexChangeLocal_transvection
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:31:43.75416+00:00
-- url     : https://prove2.me/theorems/4f36e613-69dc-415a-a7b6-848165ec16e2
-- title:
--   Division Values: index Change Local transvection
-- statement:
--   The Division Values construction uses the index Change Local transvection property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/IdxChange.lean#L566-L599
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/IdxChange.lean#L566-L599

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

theorem Formalism.DivisionValues.indexChangeLocal_transvection (v : HeightOneSpectrum R) {i j : Fin d} (hij : i ≠ j) :
    IdxChangeP v (Matrix.transvection i j (1 : K)) := by sorry
