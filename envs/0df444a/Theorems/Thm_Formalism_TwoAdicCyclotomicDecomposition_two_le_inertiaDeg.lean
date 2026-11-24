-- Prove2me | Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_two_le_inertiaDeg
-- name    : Formalism.TwoAdicCyclotomicDecomposition.two_le_inertiaDeg
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T10:30:48.192798+00:00
-- url     : https://prove2.me/theorems/166581db-c84b-4381-b588-e982a473cbe5
-- title:
--   Two Adic Cyclotomic Decomposition: two le inertia Deg
-- statement:
--   The Two Adic Cyclotomic Decomposition construction uses the two le inertia Deg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/DecompositionSubgroupIndex.lean#L68-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/DecompositionSubgroupIndex.lean#L68-L105

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

theorem Formalism.TwoAdicCyclotomicDecomposition.two_le_inertiaDeg {L : Type} [Field L] [NumberField L]
    (P : Ideal (𝓞 L)) [hP : P.IsPrime] [P.LiesOver (span {(2 : ℤ)})]
    (W : 𝓞 L) (c : ℤ) (hW : W ^ 2 = W + (c : 𝓞 L)) (hc : ¬ (2 : ℤ) ∣ c) :
    2 ≤ P.inertiaDeg ℤ := by sorry
