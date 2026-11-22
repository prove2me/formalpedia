-- Prove2me | Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_efg_L
-- name    : Formalism.TwoAdicCyclotomicDecomposition.efg_L
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T16:55:31.259484+00:00
-- url     : https://prove2.me/theorems/e11f2c6b-14db-46f2-a164-cdeca955751d
-- title:
--   Two Adic Cyclotomic Decomposition: efg L
-- statement:
--   The Two Adic Cyclotomic Decomposition construction uses the efg L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/DecompositionSubgroupIndex.lean#L174-L250
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/DecompositionSubgroupIndex.lean#L174-L250

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

theorem Formalism.TwoAdicCyclotomicDecomposition.efg_L (hG : LayerGalois) {n q d : ℕ} (hn : 1 ≤ n) (hqd : HypQD q d)
    {L : Type} [Field L] [NumberField L] {ζ a b : L} (h : IsLayer n q d ζ a b)
    (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver (span {(2 : ℤ)})] :
    P.ramificationIdx ℤ = 2 ^ (n - 1) ∧ P.inertiaDeg ℤ = 2 ∧
      (primesOver (span {(2 : ℤ)}) (𝓞 L)).ncard = 2 := by sorry
