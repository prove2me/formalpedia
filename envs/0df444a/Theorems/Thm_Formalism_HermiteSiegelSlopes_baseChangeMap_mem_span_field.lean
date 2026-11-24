-- Prove2me | Theorems.Thm_Formalism_HermiteSiegelSlopes_baseChangeMap_mem_span_field
-- name    : Formalism.HermiteSiegelSlopes.baseChangeMap_mem_span_field
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:35:05.092189+00:00
-- url     : https://prove2.me/theorems/f989f22c-83f7-4c79-b81b-335cfb6efae8
-- title:
--   Hermite Siegel Slopes: base Change Map mem span field
-- statement:
--   The Hermite Siegel Slopes construction uses the base Change Map mem span field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MonomialMeanResidues/MonomialMeanProofs/SpanEqTopAndRankOfLinearIndependent.lean#L628-L644
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MonomialMeanResidues/MonomialMeanProofs/SpanEqTopAndRankOfLinearIndependent.lean#L628-L644

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

theorem Formalism.HermiteSiegelSlopes.baseChangeMap_mem_span_field {j : ℕ} (e : Fin j → ι → F) (m : ι → F)
    (hm : m ∈ Submodule.span F (Set.range e)) :
    bcMap (E := E) m ∈ Submodule.span E (Set.range fun a => bcMap (E := E) (e a)) := by sorry
