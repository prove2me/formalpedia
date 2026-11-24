-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_PDeriv_notMem_of_rat
-- name    : Formalism.L2.Th1.F.PDeriv.notMem_of_rat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:14:36.171683+00:00
-- url     : https://prove2.me/theorems/0e703239-c25e-472f-ba0e-615445c3845b
-- title:
--   PDeriv: not Mem of rat
-- statement:
--   The PDeriv construction uses the not Mem of rat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/PDeriv.lean#L19-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/PDeriv.lean#L19-L30

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaLine
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_PDeriv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped Topology
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.PDeriv

theorem Formalism.L2.Th1.F.PDeriv.notMem_of_rat (L : PeriodPair) (α β : ℚ) {x : ℂ} (hx : x = α * L.ω₁ + β * L.ω₂)
    (h : ¬ (α.den = 1 ∧ β.den = 1)) : x ∉ L.lattice := by sorry
