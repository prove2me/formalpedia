-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_EtaEis_tendsto_one_div_linear
-- name    : Formalism.L2.Th1.F.EtaEis.tendsto_one_div_linear
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:12:43.979886+00:00
-- url     : https://prove2.me/theorems/501ce9fe-1fba-4400-aa45-39c7218b96f4
-- title:
--   Eta Eis: tendsto one div linear
-- statement:
--   The Eta Eis construction uses the tendsto one div linear property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/EtaEis.lean#L33-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/EtaEis.lean#L33-L62

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_Legendre
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_EtaEis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology
open Filter
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.EtaEis

theorem Formalism.L2.Th1.F.EtaEis.tendsto_one_div_linear (c w : ℂ) (hw : w ≠ 0) :
    Tendsto (fun N : ℕ => 1 / (c + (N : ℂ) * w)) atTop (𝓝 0) := by sorry
