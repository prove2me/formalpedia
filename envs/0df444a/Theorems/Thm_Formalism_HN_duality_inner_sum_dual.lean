-- Prove2me | Theorems.Thm_Formalism_HN_duality_inner_sum_dual
-- name    : Formalism.HN.duality_inner_sum_dual
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:54:38.749193+00:00
-- url     : https://prove2.me/theorems/36d4ad25-fd23-4dd8-bc20-3f40c9c55973
-- title:
--   HN: duality inner sum dual
-- statement:
--   The HN construction uses the duality inner sum dual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/Duality.lean#L29-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/Duality.lean#L29-L32

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

theorem Formalism.HN.duality_inner_sum_dual (v w : ι → E)
    (hvw : ∀ k i, inner ℝ (v k) (w i) = if k = i then 1 else 0) (c : ι → ℝ) (k : ι) :
    inner ℝ (v k) (∑ i, c i • w i) = c k := by sorry
