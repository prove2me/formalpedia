-- Prove2me | Theorems.Thm_Formalism_HN_duality_mem_dualZ
-- name    : Formalism.HN.duality_mem_dualZ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:50:36.674956+00:00
-- url     : https://prove2.me/theorems/683b3bd5-7341-4436-b3c8-e813964dff5f
-- title:
--   HN: duality mem dual Z
-- statement:
--   The HN construction uses the duality mem dual Z property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/Duality.lean#L15-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/Duality.lean#L15-L25

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Duality
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule
noncomputable section
open Formalism Formalism.HN
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem Formalism.HN.duality_mem_dualZ (L : Submodule ℤ E) (y : E) :
    y ∈ dualZ L ↔ y ∈ span ℝ (L : Set E) ∧ ∀ x ∈ L, ∃ n : ℤ, (n : ℝ) = inner ℝ x y := by sorry
