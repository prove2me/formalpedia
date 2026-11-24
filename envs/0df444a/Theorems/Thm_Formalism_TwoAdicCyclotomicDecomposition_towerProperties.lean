-- Prove2me | Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_towerProperties
-- name    : Formalism.TwoAdicCyclotomicDecomposition.towerProperties
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T13:32:41.398662+00:00
-- url     : https://prove2.me/theorems/76ea58c0-c4f4-42ff-8f6b-cebb07c3052d
-- title:
--   Two Adic Cyclotomic Decomposition: tower Properties
-- statement:
--   The Two Adic Cyclotomic Decomposition construction uses the tower Properties property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/TowerFieldFoundations.lean#L23-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/TowerFieldFoundations.lean#L23-L33

import Definitions.Def_Formalism_TameInertiaTowers_FinalGroup
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_Galois
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_ConjEqInvOfPowEqOne
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_DecompositionSubgroupIndex
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_OddEqOneOfSubOneMem
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.TwoAdicCyclotomicDecomposition

theorem Formalism.TwoAdicCyclotomicDecomposition.towerProperties :
    (UnitsTwoPow ∧ QuotCyclic ∧ TwoAdicOrder ∧ TwoAdicVal ∧ DecompModel ∧ GmRank ∧ GensModel ∧
      GamEModel ∧ GGModel ∧ CentralExtAbelian ∧ CommGen ∧ RankBound ∧
      NormalOrderTwoCentral ∧ TwistVal ∧ CoinvLength ∧ PGroupGen ∧ GenusModel ∧ GenusAbelian) ∧
    InvLength ∧
    (LayerExists ∧ LayerGalois ∧ LayerConj ∧ LayerReal ∧ LayerDecompTwo ∧ LayerInertiaTwo ∧
      LayerEFGTwo ∧ LayerInertiaTame ∧ LayerFrob) := by sorry
