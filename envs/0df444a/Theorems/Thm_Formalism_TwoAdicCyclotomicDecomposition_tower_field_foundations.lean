-- Prove2me | Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_tower_field_foundations
-- name    : Formalism.TwoAdicCyclotomicDecomposition.tower_field_foundations
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T13:33:15.010972+00:00
-- url     : https://prove2.me/theorems/14f62414-6b68-43cb-a10c-028d9b909aa0
-- title:
--   Two Adic Cyclotomic Decomposition: tower field foundations
-- statement:
--   The Two Adic Cyclotomic Decomposition construction uses the tower field foundations property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/TowerFieldFoundations.lean#L17-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/TowerFieldFoundations.lean#L17-L21

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

theorem Formalism.TwoAdicCyclotomicDecomposition.tower_field_foundations :
    LayerExists ∧ LayerGalois ∧ LayerConj ∧ LayerReal ∧ LayerDecompTwo ∧ LayerInertiaTwo ∧
    LayerEFGTwo ∧ LayerInertiaTame ∧ LayerFrob := by sorry
