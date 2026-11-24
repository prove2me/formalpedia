-- Prove2me | Theorems.Thm_Formalism_L2_SG_NGCut_TorsionTotientBound_le_two_totient_sq
-- name    : Formalism.L2.SG.NGCut.TorsionTotientBound.le_two_totient_sq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:39:20.136984+00:00
-- url     : https://prove2.me/theorems/cb0e2cf0-f303-4d68-a2b8-44ceb5b149fd
-- title:
--   Torsion Totient Bound: le two totient sq
-- statement:
--   The Torsion Totient Bound construction uses the le two totient sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/TorsionTotientBound.lean#L51-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/TorsionTotientBound.lean#L51-L53

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

theorem Formalism.L2.SG.NGCut.TorsionTotientBound.le_two_totient_sq (n : ℕ) : n ≤ 2 * n.totient ^ 2 := by sorry
