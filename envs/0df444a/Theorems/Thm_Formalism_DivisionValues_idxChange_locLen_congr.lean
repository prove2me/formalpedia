-- Prove2me | Theorems.Thm_Formalism_DivisionValues_idxChange_locLen_congr
-- name    : Formalism.DivisionValues.idxChange_locLen_congr
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:31:51.059143+00:00
-- url     : https://prove2.me/theorems/d3840e2f-d441-4784-993d-3bd43d95f7eb
-- title:
--   Division Values: idx Change loc Len congr
-- statement:
--   The Division Values construction uses the idx Change loc Len congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/IdxChange.lean#L177-L180
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/IdxChange.lean#L177-L180

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

theorem Formalism.DivisionValues.idxChange_locLen_congr (p : Ideal R) [p.IsPrime] {X X' Y Y' : Submodule R (Fin d → K)}
    (hX : localization₂ p X = localization₂ p X') (hY : localization₂ p Y = localization₂ p Y') : locLen p X Y = locLen p X' Y' := by sorry
