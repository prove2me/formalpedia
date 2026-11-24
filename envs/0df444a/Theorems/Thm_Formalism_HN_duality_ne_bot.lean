-- Prove2me | Theorems.Thm_Formalism_HN_duality_ne_bot
-- name    : Formalism.HN.duality_ne_bot
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:54:29.452393+00:00
-- url     : https://prove2.me/theorems/0a1dbd7b-323b-4ef2-9bef-cac957a6b04f
-- title:
--   HN: duality ne bot
-- statement:
--   The HN construction uses the duality ne bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/Duality.lean#L193-L200
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/Duality.lean#L193-L200

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
variable [FiniteDimensional ℝ E]

theorem Formalism.HN.duality_ne_bot (L : Submodule ℤ E) [DiscreteTopology L] (hL : L ≠ ⊥) : dualZ L ≠ ⊥ := by sorry
