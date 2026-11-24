-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_PeriodLatticeBasisLemmas_qp_two_mul
-- name    : Formalism.L2.Th1.F.PeriodLatticeBasisLemmas.qp_two_mul
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T09:47:54.063539+00:00
-- url     : https://prove2.me/theorems/2a5e54bf-a538-415d-a1f8-2aff80ebab52
-- title:
--   Period Lattice Basis Lemmas: qp two mul
-- statement:
--   The Period Lattice Basis Lemmas construction uses the qp two mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/SigmaQuasi.lean#L158-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/SigmaQuasi.lean#L158-L169

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

theorem Formalism.L2.Th1.F.PeriodLatticeBasisLemmas.qp_two_mul (L : PeriodPair) {ω c : ℂ} (h : QP L ω c) (hc : c ^ 2 = 1) : QP L (2 * ω) 1 := by sorry
