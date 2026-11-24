-- Prove2me | Theorems.Thm_Formalism_RepresentationBoundsCohomology_LOC_span_killed
-- name    : Formalism.RepresentationBoundsCohomology.LOC.span_killed
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T10:27:31.240846+00:00
-- url     : https://prove2.me/theorems/8158800e-5725-4c7b-a9a6-c632c89c16a0
-- title:
--   LOC: span killed
-- statement:
--   The LOC construction uses the span killed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WachLatticeTwists/LatticeDualFibres/LatticeDualProofs/QuotLen.lean#L115-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WachLatticeTwists/LatticeDualFibres/LatticeDualProofs/QuotLen.lean#L115-L129

import Definitions.Def_Formalism_WachLatticeTwists_LatticeDualFibres_Statement
import Definitions.Def_Formalism_WachLatticeTwists_TorsionLengthCounts_RowCol
import Definitions.Def_Formalism_WachLatticeTwists_TorsionLengthCounts_SubmoduleLengthBoundStatement
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthEqKerAddRange
import Definitions.Def_Formalism_WachLatticeTwists_LatticeDualFibres_LatticeDualProofs_QuotLen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open Formalism.NG (KO annih)
noncomputable section
open Formalism Formalism.RepresentationBoundsCohomology Formalism.RepresentationBoundsCohomology.LOC
open Module
variable {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem Formalism.RepresentationBoundsCohomology.LOC.span_killed {N : Type u} [AddCommGroup N] [Module O N]
    (ht : ∀ x : N, ∃ c : O, c ≠ 0 ∧ c • x = 0) (t : Finset N) :
    ∃ c : O, c ≠ 0 ∧ ∀ n ∈ Submodule.span O (t : Set N), c • n = 0 := by sorry
