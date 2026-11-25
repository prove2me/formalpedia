-- Prove2me | Theorems.Thm_Formalism_L2_Th1_E_AddThm_exists_finite_part_one_idele_split_congruence_quotient
-- name    : Formalism.L2.Th1.E.AddThm.exists_finite_part_one_idele_split_congruence_quotient
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T07:05:08.490722+00:00
-- url     : https://prove2.me/theorems/b323ee40-bece-4b61-bb01-d2879e2aeda2
-- title:
--   Add Thm: exists finite part one idele split congruence quotient
-- statement:
--   The Add Thm construction uses the exists finite part one idele split congruence quotient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/NonsingularJetNorms/ExistsFinitePartOneIdeleSplitCongruenceQuotient.lean#L117-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/NonsingularJetNorms/ExistsFinitePartOneIdeleSplitCongruenceQuotient.lean#L117-L129

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

theorem Formalism.L2.Th1.E.AddThm.exists_finite_part_one_idele_split_congruence_quotient (s : ℂ) : ∃ u : ℂ, 2 * u ∉ L.lattice ∧ s + u ∉ L.lattice ∧ s - u ∉ L.lattice := by sorry
