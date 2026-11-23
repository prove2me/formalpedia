-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_WeierstrassZetaQuasiPeriod_add_notMem
-- name    : Formalism.L2.Th1.F.WeierstrassZetaQuasiPeriod.add_notMem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:27:30.847283+00:00
-- url     : https://prove2.me/theorems/45a437cb-aa7c-4140-873b-1fb368598fd8
-- title:
--   Weierstrass Zeta Quasi Period: add not Mem
-- statement:
--   The Weierstrass Zeta Quasi Period construction uses the add not Mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/ZetaQuasi.lean#L16-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/ZetaQuasi.lean#L16-L17

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_Legendre
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_ZetaQuasi
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
open Formalism.L2.Th1.F.WeierstrassZetaQuasiPeriod

theorem Formalism.L2.Th1.F.WeierstrassZetaQuasiPeriod.add_notMem {L : PeriodPair} {ω z : ℂ} (hω : ω ∈ L.lattice) (hz : z ∉ L.lattice) :
    z + ω ∉ L.lattice := by sorry
