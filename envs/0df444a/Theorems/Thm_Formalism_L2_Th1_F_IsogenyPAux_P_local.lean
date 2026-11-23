-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_IsogenyPAux_P_local
-- name    : Formalism.L2.Th1.F.IsogenyPAux.P_local
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:29:38.634302+00:00
-- url     : https://prove2.me/theorems/5a098d6b-c4ed-47b0-901c-bf52610da9f0
-- title:
--   Isogeny PAux: P local
-- statement:
--   The Isogeny PAux construction uses the P local property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/IsogenyP.lean#L10-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/IsogenyP.lean#L10-L16

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_TranslateProduct
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_Elliptic
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_IsogenyP
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.IsogenyPAux

theorem Formalism.L2.Th1.F.IsogenyPAux.P_local (L : PeriodPair) (ω : ℂ) (hω : ω ∈ L.lattice) (w : ℂ) :
    L.weierstrassP w = L.weierstrassPExcept 0 (w - ω) + 1 / (w - ω) ^ 2 := by sorry
