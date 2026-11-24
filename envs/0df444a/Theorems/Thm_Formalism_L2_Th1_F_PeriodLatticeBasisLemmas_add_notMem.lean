-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_PeriodLatticeBasisLemmas_add_notMem
-- name    : Formalism.L2.Th1.F.PeriodLatticeBasisLemmas.add_notMem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:58:23.890458+00:00
-- url     : https://prove2.me/theorems/02670df9-4395-405b-ad12-76155d7cd7a7
-- title:
--   Period Lattice Basis Lemmas: add not Mem
-- statement:
--   The Period Lattice Basis Lemmas construction uses the add not Mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/SigmaQuasi.lean#L69-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/SigmaQuasi.lean#L69-L74

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

theorem Formalism.L2.Th1.F.PeriodLatticeBasisLemmas.add_notMem {L : PeriodPair} {ω z : ℂ} (hω : ω ∈ L.lattice) (hz : z ∉ L.lattice) :
    z + ω ∉ L.lattice := by sorry
