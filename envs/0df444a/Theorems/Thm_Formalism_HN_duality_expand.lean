-- Prove2me | Theorems.Thm_Formalism_HN_duality_expand
-- name    : Formalism.HN.duality_expand
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:54:28.03663+00:00
-- url     : https://prove2.me/theorems/7ef36e17-affb-4948-af61-71830dbed908
-- title:
--   HN: duality expand
-- statement:
--   The HN construction uses the duality expand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/Duality.lean#L48-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/Duality.lean#L48-L57

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
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem Formalism.HN.duality_expand (v w : ι → E) (hw : ∀ i, w i ∈ span ℝ (Set.range v))
    (hvw : ∀ k i, inner ℝ (v k) (w i) = if k = i then 1 else 0) {y : E}
    (hy : y ∈ span ℝ (Set.range v)) : y = ∑ k, inner ℝ (v k) y • w k := by sorry
