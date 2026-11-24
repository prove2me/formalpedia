-- Prove2me | Theorems.Thm_Formalism_HermiteSiegelSlopes_bc_index
-- name    : Formalism.HermiteSiegelSlopes.bc_index
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:34:50.223799+00:00
-- url     : https://prove2.me/theorems/bdcf9933-e828-440d-99c2-f8b5b1157ce0
-- title:
--   Hermite Siegel Slopes: bc index
-- statement:
--   The Hermite Siegel Slopes construction uses the bc index property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MonomialMeanResidues/MonomialMeanProofs/SpanEqTopAndRankOfLinearIndependent.lean#L561-L609
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MonomialMeanResidues/MonomialMeanProofs/SpanEqTopAndRankOfLinearIndependent.lean#L561-L609

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

theorem Formalism.HermiteSiegelSlopes.bc_index {j : ℕ} (e : Fin j → ι → F) (he : LinearIndependent F e)
    (M : Submodule (𝓞 F) (ι → F)) (hM : M.FG) (hle : Submodule.span (𝓞 F) (Set.range e) ≤ M)
    (hsp : (M : Set (ι → F)) ⊆ Submodule.span F (Set.range e)) :
    (Submodule.span (𝓞 E) (Set.range fun a => bcMap (E := E) (e a))).toAddSubgroup.relIndex
        (bcLat (E := E) M).toAddSubgroup =
      ((Submodule.span (𝓞 F) (Set.range e)).toAddSubgroup.relIndex M.toAddSubgroup) ^ finrank F E := by sorry
