-- Prove2me | Theorems.Thm_Formalism_HN_exists_decomp_of_mem_iSup
-- name    : Formalism.HN.exists_decomp_of_mem_iSup
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:54:23.554259+00:00
-- url     : https://prove2.me/theorems/3e61b090-e532-41f2-9cf4-a31a04745523
-- title:
--   HN: exists decomp of mem i Sup
-- statement:
--   The HN construction uses the exists decomp of mem i Sup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/HtImage.lean#L34-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/HtImage.lean#L34-L49

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

theorem Formalism.HN.exists_decomp_of_mem_iSup {P E : Type*} [Fintype P] [AddCommGroup E] [Module ℝ E]
    (p : P → Submodule ℝ E) {x : E} (hx : x ∈ ⨆ v, p v) :
    ∃ f : P → E, (∀ v, f v ∈ p v) ∧ ∑ v, f v = x := by sorry
