-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_cm_half_lattice_iff
-- name    : Formalism.L2.Th1.F.cm_half_lattice_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:58:30.0588+00:00
-- url     : https://prove2.me/theorems/7af154fd-e871-4954-ac59-8df95b1747d8
-- title:
--   F: cm half lattice iff
-- statement:
--   The F construction uses the cm half lattice iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/CmAlternatingForm.lean#L223-L238
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/CmAlternatingForm.lean#L223-L238

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_CMQuasiPeriodConst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_CmAlternatingForm
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
open Cm1

theorem Formalism.L2.Th1.F.cm_half_lattice_iff : CMHalfLatticeIff := by sorry
