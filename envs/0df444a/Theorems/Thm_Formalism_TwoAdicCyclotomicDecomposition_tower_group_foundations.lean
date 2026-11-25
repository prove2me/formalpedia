-- Prove2me | Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_tower_group_foundations
-- name    : Formalism.TwoAdicCyclotomicDecomposition.tower_group_foundations
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:54:09.941621+00:00
-- url     : https://prove2.me/theorems/2f985ccd-c9db-4565-8b5f-5b87c5471b59
-- title:
--   Two Adic Cyclotomic Decomposition: tower group foundations
-- statement:
--   The Two Adic Cyclotomic Decomposition construction uses the tower group foundations property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/FinalGroup.lean#L10-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/FinalGroup.lean#L10-L16

import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_OrderOfThreeUnitsTwoPow
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_TwoAdic
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_MemDecompositionSubgroupIff
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_NegOneNeOneUnitsZmodFour
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_Groups
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_NormalOrderTwoCentral
import Definitions.Def_Formalism_TameInertiaTowers_FinalGroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.TwoAdicCyclotomicDecomposition

theorem Formalism.TwoAdicCyclotomicDecomposition.tower_group_foundations :
    UnitsTwoPow ∧ QuotCyclic ∧ TwoAdicOrder ∧ TwoAdicVal ∧ DecompModel ∧ GmRank ∧ GensModel ∧
    GamEModel ∧ GGModel ∧ CentralExtAbelian ∧ CommGen ∧ RankBound ∧
    NormalOrderTwoCentral ∧ TwistVal ∧ CoinvLength ∧ PGroupGen ∧ GenusModel ∧ GenusAbelian := by sorry
