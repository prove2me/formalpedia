-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_EtaEis_summable_inv_sq
-- name    : Formalism.L2.Th1.F.EtaEis.summable_inv_sq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:51:30.489122+00:00
-- url     : https://prove2.me/theorems/d451c565-2647-4245-957a-cf388aae853a
-- title:
--   Eta Eis: summable inv sq
-- statement:
--   The Eta Eis construction uses the summable inv sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/EtaEis.lean#L96-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/EtaEis.lean#L96-L104

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

theorem Formalism.L2.Th1.F.EtaEis.summable_inv_sq (u v : ℂ) (hu : u ≠ 0) (n : ℤ) :
    Summable fun m : ℤ => 1 / ((m : ℂ) * u + (n : ℂ) * v) ^ 2 := by sorry
