-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_S2IsogenyPsi_add_dom
-- name    : Formalism.L2.Th1.F.S2IsogenyPsi.add_dom
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:26:52.5048+00:00
-- url     : https://prove2.me/theorems/65979378-4f29-4b71-a04e-d3e0f544d8d0
-- title:
--   S2 Isogeny Psi: add dom
-- statement:
--   The S2 Isogeny Psi construction uses the add dom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/QuasiPeriodConstIsogeny.lean#L40-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/QuasiPeriodConstIsogeny.lean#L40-L46

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

theorem Formalism.L2.Th1.F.S2IsogenyPsi.add_dom {L : PeriodPair} {α z P : ℂ} (hP : α * P ∈ L.lattice) (hz : α * z ∉ L.lattice) :
    α * (z + P) ∉ L.lattice := by sorry
