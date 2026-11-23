-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_IsogenyPAux_eventually_notMem
-- name    : Formalism.L2.Th1.F.IsogenyPAux.eventually_notMem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:25:56.767262+00:00
-- url     : https://prove2.me/theorems/9479adfe-9280-4bed-b72f-3c3e7b3289d3
-- title:
--   Isogeny PAux: eventually not Mem
-- statement:
--   The Isogeny PAux construction uses the eventually not Mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/IsogenyP.lean#L29-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/IsogenyP.lean#L29-L36

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

theorem Formalism.L2.Th1.F.IsogenyPAux.eventually_notMem (L : PeriodPair) (α z : ℂ) (hα : α ≠ 0) :
    ∀ᶠ w in 𝓝[≠] z, α * w ∉ L.lattice := by sorry
