-- Prove2me | Theorems.Thm_Formalism_NuclearRankWeightBounds_P_descend_mk
-- name    : Formalism.NuclearRankWeightBounds.P.descend_mk
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:51:47.843519+00:00
-- url     : https://prove2.me/theorems/9ed66301-8d43-57f8-8ae3-9e1bad154f31
-- title:
--   P: descend mk
-- statement:
--   The P construction uses the descend mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogSumExpBounds/CharacterSumPhase/KappaModulusHolds.lean#L10-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogSumExpBounds/CharacterSumPhase/KappaModulusHolds.lean#L10-L16

import Definitions.Def_Formalism_LogSumExpBounds_StatementC
import Definitions.Def_Formalism_LogSumExpBounds_CharacterSumPhase_KappaModulusHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.NuclearRankWeightBounds Formalism.NuclearRankWeightBounds.P
open Matrix Formalism.NuclearRankWeightBounds.C
variable {RR : Type*} {K : Type*} [CommRing RR] [CommRing K] [Algebra RR K]

theorem Formalism.NuclearRankWeightBounds.P.descend_mk {k : ℕ} (Z : Matrix (Fin k) (Fin k) RR) (r : Fin k → K)
    (hZ : LinearMap.range Z.mulVecLin ≤ LinearMap.ker (rowInvMod K Z r)) (v : Fin k → RR) :
    descend K Z r (Submodule.Quotient.mk v) = rowInvMod K Z r v := by sorry
