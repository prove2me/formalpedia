-- Prove2me | Theorems.Thm_Formalism_L2_Th1_E_Ser_rootInt
-- name    : Formalism.L2.Th1.E.Ser.rootInt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:18:49.557722+00:00
-- url     : https://prove2.me/theorems/0b42e5a4-1dc4-426f-ab23-6d9c56c90d9b
-- title:
--   Ser: root Int
-- statement:
--   The Ser construction uses the root Int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/NonsingularJetNorms/Series.lean#L169-L209
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/NonsingularJetNorms/Series.lean#L169-L209

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

theorem Formalism.L2.Th1.E.Ser.rootInt {N : ℕ} {g : K⟦X⟧} (hN : ‖(N : K)‖ = 1) (h0 : constantCoeff g = 1)
    (hg : IntS (g ^ N)) : IntS g := by sorry
