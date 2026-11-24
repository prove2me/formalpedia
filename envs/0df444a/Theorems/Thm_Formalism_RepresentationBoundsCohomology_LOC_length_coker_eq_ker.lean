-- Prove2me | Theorems.Thm_Formalism_RepresentationBoundsCohomology_LOC_length_coker_eq_ker
-- name    : Formalism.RepresentationBoundsCohomology.LOC.length_coker_eq_ker
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T10:27:30.685978+00:00
-- url     : https://prove2.me/theorems/bb15c4f2-8028-44c6-b295-b7f1f441d05f
-- title:
--   LOC: length coker eq ker
-- statement:
--   The LOC construction uses the length coker eq ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WachLatticeTwists/LatticeDualFibres/LatticeDualProofs/QuotLen.lean#L76-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WachLatticeTwists/LatticeDualFibres/LatticeDualProofs/QuotLen.lean#L76-L91

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
variable {O : Type u} [CommRing O]

theorem Formalism.RepresentationBoundsCohomology.LOC.length_coker_eq_ker (a : O) {M : Type u} [AddCommGroup M] [Module O M]
    (hM : Module.length O M ≠ ⊤) :
    Module.length O (M ⧸ mulSub a M) = Module.length O (LinearMap.ker (LinearMap.lsmul O M a)) := by sorry
