-- Prove2me | Theorems.Thm_Formalism_HermiteSiegelSlopes_baseChangeMap_smul_field
-- name    : Formalism.HermiteSiegelSlopes.baseChangeMap_smul_field
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:35:20.870862+00:00
-- url     : https://prove2.me/theorems/52f73ed9-1dc1-48ef-a773-354c60e7a8ee
-- title:
--   Hermite Siegel Slopes: base Change Map smul field
-- statement:
--   The Hermite Siegel Slopes construction uses the base Change Map smul field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MonomialMeanResidues/MonomialMeanProofs/SpanEqTopAndRankOfLinearIndependent.lean#L620-L622
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MonomialMeanResidues/MonomialMeanProofs/SpanEqTopAndRankOfLinearIndependent.lean#L620-L622

import Definitions.Def_Formalism_MonomialMeanResidues_FilteredDegree
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Definitions.Def_Formalism_MonomialMeanResidues_MonomialMeanProofs_SpanEqTopAndRankOfLinearIndependent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Finset
noncomputable section
open Formalism Formalism.HermiteSiegelSlopes
open Formalism.HN
open scoped nonZeroDivisors
open IsDedekindDomain
variable {F E ι : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem Formalism.HermiteSiegelSlopes.baseChangeMap_smul_field (c : F) (x : ι → F) : bcMap (E := E) (c • x) = algebraMap F E c • bcMap x := by sorry
