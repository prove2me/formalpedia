-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_S2IsogenyPsi_notMem_of_dom
-- name    : Formalism.L2.Th1.F.S2IsogenyPsi.notMem_of_dom
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:26:53.161769+00:00
-- url     : https://prove2.me/theorems/6461fbf2-7986-4550-9fc7-1e09e4283ce7
-- title:
--   S2 Isogeny Psi: not Mem of dom
-- statement:
--   The S2 Isogeny Psi construction uses the not Mem of dom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/QuasiPeriodConstIsogeny.lean#L37-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/QuasiPeriodConstIsogeny.lean#L37-L38

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_QuasiPeriodConstIsogeny
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.S2IsogenyPsi

theorem Formalism.L2.Th1.F.S2IsogenyPsi.notMem_of_dom {L : PeriodPair} {α z : ℂ} (hst : MulStable L α) (hz : α * z ∉ L.lattice) :
    z ∉ L.lattice := by sorry
