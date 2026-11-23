-- Prove2me | Theorems.Thm_Formalism_RepresentationBoundsCohomology_LOC_mem_mulSub
-- name    : Formalism.RepresentationBoundsCohomology.LOC.mem_mulSub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:28:28.524007+00:00
-- url     : https://prove2.me/theorems/dbbc1b4d-a43d-4308-849e-0f0e3f5a7b71
-- title:
--   LOC: mem mul Sub
-- statement:
--   The LOC construction uses the mem mul Sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WachLatticeTwists/LatticeDualFibres/LatticeDualProofs/QuotLen.lean#L20-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WachLatticeTwists/LatticeDualFibres/LatticeDualProofs/QuotLen.lean#L20-L22

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

theorem Formalism.RepresentationBoundsCohomology.LOC.mem_mulSub {a : O} {M : Type u} [AddCommGroup M] [Module O M] (x : M) :
    x ∈ mulSub a M ↔ ∃ m, a • m = x := by sorry
