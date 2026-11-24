-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_PeriodLatticeBasisLemmas_semiChar_ne_zero
-- name    : Formalism.L2.Th1.F.PeriodLatticeBasisLemmas.semiChar_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:56:40.991888+00:00
-- url     : https://prove2.me/theorems/cc6b68d1-2295-4ab5-b71b-def73bf8e590
-- title:
--   Period Lattice Basis Lemmas: semi Char ne zero
-- statement:
--   The Period Lattice Basis Lemmas construction uses the semi Char ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/SigmaQuasi.lean#L175-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/SigmaQuasi.lean#L175-L177

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_Legendre
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_SigmaQuasi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.PeriodLatticeBasisLemmas

theorem Formalism.L2.Th1.F.PeriodLatticeBasisLemmas.semiChar_ne_zero (L : PeriodPair) (ω : ℂ) : semiChar L ω ≠ 0 := by sorry
