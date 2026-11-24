-- Prove2me | Theorems.Thm_Formalism_HN_duality_basic
-- name    : Formalism.HN.duality_basic
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:36:27.790793+00:00
-- url     : https://prove2.me/theorems/a9ef321c-7207-4c78-ab38-e299f72c458f
-- title:
--   HN: duality basic
-- statement:
--   The HN construction uses the duality basic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/Duality.lean#L155-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/Duality.lean#L155-L191

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

theorem Formalism.HN.duality_basic (L : Submodule ℤ E) [DiscreteTopology L] :
    DiscreteTopology (dualZ L) ∧ Formalism.F.rk (dualZ L) = Formalism.F.rk L ∧
    Formalism.F.deg (dualZ L) = - Formalism.F.deg L ∧ dualZ (dualZ L) = L := by sorry
