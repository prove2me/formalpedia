-- Prove2me | Theorems.Thm_Formalism_DivisionValues_idxChange_hcompl_le_conj
-- name    : Formalism.DivisionValues.idxChange_hcompl_le_conj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:31:33.309471+00:00
-- url     : https://prove2.me/theorems/e32046c1-706a-4ffd-876f-18c4b83d3074
-- title:
--   Division Values: idx Change hcompl le conj
-- statement:
--   The Division Values construction uses the idx Change hcompl le conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/IdxChange.lean#L657-L669
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/IdxChange.lean#L657-L669

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
open NumberField
variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem Formalism.DivisionValues.idxChange_hcompl_le_conj (w : HeightOneSpectrum (𝓞 K)) :
    hcompl (K := K) w.asIdeal ≤ (conjPl w).asIdeal.primeCompl := by sorry
