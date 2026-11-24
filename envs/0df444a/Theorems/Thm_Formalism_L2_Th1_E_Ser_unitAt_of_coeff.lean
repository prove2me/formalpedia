-- Prove2me | Theorems.Thm_Formalism_L2_Th1_E_Ser_unitAt_of_coeff
-- name    : Formalism.L2.Th1.E.Ser.unitAt_of_coeff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:08:49.642903+00:00
-- url     : https://prove2.me/theorems/117c4d0a-cab2-45ba-9c4d-cce21418c7d0
-- title:
--   Ser: unit At of coeff
-- statement:
--   The Ser construction uses the unit At of coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/NonsingularJetNorms/Series.lean#L125-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/NonsingularJetNorms/Series.lean#L125-L148

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementU
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_Series
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries Finset
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.E
open Formalism.L2.Th1.E.Ser
variable {K : Type} [NormedField K] [IsUltrametricDist K]

theorem Formalism.L2.Th1.E.Ser.unitAt_of_coeff {k : ℕ} {f : K⟦X⟧} (hf : IntS f) (h0 : ∀ i, i < k → coeff i f = 0)
    (hk : ‖coeff k f‖ = 1) : UnitAt k f := by sorry
