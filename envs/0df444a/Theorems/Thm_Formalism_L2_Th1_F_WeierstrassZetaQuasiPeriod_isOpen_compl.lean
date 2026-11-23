-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_WeierstrassZetaQuasiPeriod_isOpen_compl
-- name    : Formalism.L2.Th1.F.WeierstrassZetaQuasiPeriod.isOpen_compl
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:28:47.530906+00:00
-- url     : https://prove2.me/theorems/4a6b6a33-b332-4730-8d61-cd19c3ec53cc
-- title:
--   Weierstrass Zeta Quasi Period: is Open compl
-- statement:
--   The Weierstrass Zeta Quasi Period construction uses the is Open compl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/ZetaQuasi.lean#L9-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/ZetaQuasi.lean#L9-L10

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

theorem Formalism.L2.Th1.F.WeierstrassZetaQuasiPeriod.isOpen_compl (L : PeriodPair) : IsOpen ((L.lattice : Set ℂ)ᶜ) := by sorry
