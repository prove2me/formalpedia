-- Prove2me | Theorems.Thm_Formalism_HN_mem_place_part_iff
-- name    : Formalism.HN.mem_place_part_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:33:51.529091+00:00
-- url     : https://prove2.me/theorems/28c8a071-94dc-4e40-9c99-3ffc79a3124b
-- title:
--   HN: mem place part iff
-- statement:
--   The HN construction uses the mem place part iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/HtImage.lean#L16-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/HtImage.lean#L16-L19

import Definitions.Def_Formalism_HarderNarasimhan_StatementPl
import Definitions.Def_Formalism_HarderNarasimhan_DefsPl
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PlaceSplit
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_GramBlock
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HtImage
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.HN

theorem Formalism.HN.mem_place_part_iff {P ι : Type*} [Fintype P] [Fintype ι] {v : P}
    {x : EuclideanSpace ℝ (P × ι × Fin 2)} :
    x ∈ placePart v ↔ ∀ p : P × ι × Fin 2, p.1 ≠ v → x p = 0 := by sorry
