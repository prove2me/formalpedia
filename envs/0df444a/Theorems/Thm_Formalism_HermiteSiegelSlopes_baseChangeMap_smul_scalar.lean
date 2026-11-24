-- Prove2me | Theorems.Thm_Formalism_HermiteSiegelSlopes_baseChangeMap_smul_scalar
-- name    : Formalism.HermiteSiegelSlopes.baseChangeMap_smul_scalar
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:35:08.758334+00:00
-- url     : https://prove2.me/theorems/99b03cfa-5f44-4109-aa1b-52f7edd645ec
-- title:
--   Hermite Siegel Slopes: base Change Map smul scalar
-- statement:
--   The Hermite Siegel Slopes construction uses the base Change Map smul scalar property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MonomialMeanResidues/MonomialMeanProofs/SpanEqTopAndRankOfLinearIndependent.lean#L270-L273
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MonomialMeanResidues/MonomialMeanProofs/SpanEqTopAndRankOfLinearIndependent.lean#L270-L273

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
  [Fintype ι] [DecidableEq ι]

theorem Formalism.HermiteSiegelSlopes.baseChangeMap_smul_scalar (s : F) (x : ι → F) :
    bcMap (E := E) (s • x) = algebraMap F E s • bcMap x := by sorry
