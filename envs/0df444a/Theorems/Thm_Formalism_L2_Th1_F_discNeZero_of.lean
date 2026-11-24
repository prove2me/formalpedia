-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_discNeZero_of
-- name    : Formalism.L2.Th1.F.discNeZero_of
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:55:40.176864+00:00
-- url     : https://prove2.me/theorems/7a7bbefd-17f5-4133-a243-5a49f1d9c10c
-- title:
--   F: disc Ne Zero of
-- statement:
--   The F construction uses the disc Ne Zero of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/PDeriv.lean#L89-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/PDeriv.lean#L89-L123

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaLine
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_PDeriv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped Topology
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open PDeriv

theorem Formalism.L2.Th1.F.discNeZero_of (hp : PDerivZero) (hi : PInjective) : DiscNeZero := by sorry
