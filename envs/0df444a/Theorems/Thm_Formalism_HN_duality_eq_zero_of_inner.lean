-- Prove2me | Theorems.Thm_Formalism_HN_duality_eq_zero_of_inner
-- name    : Formalism.HN.duality_eq_zero_of_inner
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:54:46.240802+00:00
-- url     : https://prove2.me/theorems/e858f229-08ad-4f34-889f-0dc4220d03de
-- title:
--   HN: duality eq zero of inner
-- statement:
--   The HN construction uses the duality eq zero of inner property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/Duality.lean#L34-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/Duality.lean#L34-L46

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

theorem Formalism.HN.duality_eq_zero_of_inner (v : ι → E) {z : E} (hz : z ∈ span ℝ (Set.range v))
    (h : ∀ k, inner ℝ (v k) z = 0) : z = 0 := by sorry
