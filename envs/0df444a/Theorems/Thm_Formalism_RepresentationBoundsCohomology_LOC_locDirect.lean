-- Prove2me | Theorems.Thm_Formalism_RepresentationBoundsCohomology_LOC_locDirect
-- name    : Formalism.RepresentationBoundsCohomology.LOC.locDirect
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T10:27:20.616052+00:00
-- url     : https://prove2.me/theorems/364d13f6-c417-4aaa-a4a3-1f16caea1f96
-- title:
--   LOC: loc Direct
-- statement:
--   The LOC construction uses the loc Direct property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WachLatticeTwists/LatticeDualFibres/LatticeDualProofs/LocDualOrth.lean#L18-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WachLatticeTwists/LatticeDualFibres/LatticeDualProofs/LocDualOrth.lean#L18-L22

import Definitions.Def_Formalism_WachLatticeTwists_LatticeDualFibres_Statement
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthEqKerAddRange
import Definitions.Def_Formalism_WachLatticeTwists_LatticeDualFibres_LatticeDualProofs_LocDualOrth
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

theorem Formalism.RepresentationBoundsCohomology.LOC.locDirect : StatLocDirect.{u} := by sorry
