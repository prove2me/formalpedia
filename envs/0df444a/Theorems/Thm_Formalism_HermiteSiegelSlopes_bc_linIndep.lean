-- Prove2me | Theorems.Thm_Formalism_HermiteSiegelSlopes_bc_linIndep
-- name    : Formalism.HermiteSiegelSlopes.bc_linIndep
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T03:01:13.949859+00:00
-- url     : https://prove2.me/theorems/8cc2115d-9d9a-4095-96c3-4e43f0d59a12
-- title:
--   Hermite Siegel Slopes: bc lin Indep
-- statement:
--   The Hermite Siegel Slopes construction uses the bc lin Indep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MonomialMeanResidues/MonomialMeanProofs/SpanEqTopAndRankOfLinearIndependent.lean#L133-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MonomialMeanResidues/MonomialMeanProofs/SpanEqTopAndRankOfLinearIndependent.lean#L133-L167

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

theorem Formalism.HermiteSiegelSlopes.bc_linIndep {j : ℕ} (e : Fin j → ι → F) (he : LinearIndependent F e) :
    LinearIndependent E (fun a => bcMap (E := E) (e a)) := by sorry
