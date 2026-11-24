-- Prove2me | Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_layerInertiaTwo_of
-- name    : Formalism.TwoAdicCyclotomicDecomposition.layerInertiaTwo_of
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T10:30:08.0108+00:00
-- url     : https://prove2.me/theorems/d61089b9-5398-4018-9934-ed95c47765af
-- title:
--   Two Adic Cyclotomic Decomposition: layer Inertia Two of
-- statement:
--   The Two Adic Cyclotomic Decomposition construction uses the layer Inertia Two of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/DecompositionSubgroupIndex.lean#L285-L322
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/DecompositionSubgroupIndex.lean#L285-L322

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementField
import Definitions.Def_Lemmata_FirstBlockLemmaE_Imports
import Definitions.Def_Lemmata_GeneralBFactRightTerForm_Imports
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_DecompositionSubgroupIndex
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Ideal
open scoped Pointwise
noncomputable section
open Formalism Formalism.TwoAdicCyclotomicDecomposition

theorem Formalism.TwoAdicCyclotomicDecomposition.layerInertiaTwo_of (hG : LayerGalois) : LayerInertiaTwo := by sorry
