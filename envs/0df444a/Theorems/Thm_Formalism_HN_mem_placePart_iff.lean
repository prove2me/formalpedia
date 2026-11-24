-- Prove2me | Theorems.Thm_Formalism_HN_mem_placePart_iff
-- name    : Formalism.HN.mem_placePart_iff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:29:06.544964+00:00
-- url     : https://prove2.me/theorems/08f35252-34a7-4dbe-b9fd-8b8f550a9379
-- title:
--   HN: mem place Part iff
-- statement:
--   The HN construction uses the mem place Part iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/RescaleCovol.lean#L24-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/RescaleCovol.lean#L24-L27

import Definitions.Def_Formalism_HarderNarasimhan_DefsPl
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PlaceSplit
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_GramBlock
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_RescaleCovol
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

theorem Formalism.HN.mem_placePart_iff {P ι : Type*} [Fintype P] [Fintype ι] (v : P)
    (x : EuclideanSpace ℝ (P × ι × Fin 2)) :
    x ∈ placePart (ι := ι) v ↔ ∀ p : P × ι × Fin 2, p.1 ≠ v → x p = 0 := by sorry
