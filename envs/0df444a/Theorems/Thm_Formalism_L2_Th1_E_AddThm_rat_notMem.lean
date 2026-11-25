-- Prove2me | Theorems.Thm_Formalism_L2_Th1_E_AddThm_rat_notMem
-- name    : Formalism.L2.Th1.E.AddThm.rat_notMem
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T07:17:08.589794+00:00
-- url     : https://prove2.me/theorems/ae122468-b559-5f7c-85e6-3638b8cacbf7
-- title:
--   Add Thm: rat not Mem
-- statement:
--   The Add Thm construction uses the rat not Mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/NonsingularJetNorms/ExistsFinitePartOneIdeleSplitCongruenceQuotient.lean#L111-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/NonsingularJetNorms/ExistsFinitePartOneIdeleSplitCongruenceQuotient.lean#L111-L115

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_ExistsFinitePartOneIdeleSplitCongruenceQuotient
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.E
open Formalism.L2.Th1.E.AddThm
open Formalism.L2.Th1
variable (L : PeriodPair)

theorem Formalism.L2.Th1.E.AddThm.rat_notMem (q : ℚ) (hq : q.den ≠ 1) (x : ℂ) (hx : x = (q : ℂ) * L.ω₁) : x ∉ L.lattice := by sorry
