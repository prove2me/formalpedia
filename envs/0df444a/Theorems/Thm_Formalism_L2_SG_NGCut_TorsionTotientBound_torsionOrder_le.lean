-- Prove2me | Theorems.Thm_Formalism_L2_SG_NGCut_TorsionTotientBound_torsionOrder_le
-- name    : Formalism.L2.SG.NGCut.TorsionTotientBound.torsionOrder_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T03:54:33.38529+00:00
-- url     : https://prove2.me/theorems/28267907-ea43-4093-a53a-baa685cca027
-- title:
--   Torsion Totient Bound: torsion Order le
-- statement:
--   The Torsion Totient Bound construction uses the torsion Order le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/TorsionTotientBound.lean#L55-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/TorsionTotientBound.lean#L55-L78

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_TorsionTotientBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.NGCut Formalism.L2.SG.NGCut.TorsionTotientBound

theorem Formalism.L2.SG.NGCut.TorsionTotientBound.torsionOrder_le (E : Type) [Field E] [NumberField E] :
    Units.torsionOrder E ≤ 2 * (Module.finrank ℚ E) ^ 2 := by sorry
