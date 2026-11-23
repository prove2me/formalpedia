-- Prove2me | Theorems.Thm_Formalism_RankSupermodularCovolume_covol_eq_relIndex_mul_covol
-- name    : Formalism.RankSupermodularCovolume.covol_eq_relIndex_mul_covol
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:57:55.756396+00:00
-- url     : https://prove2.me/theorems/24af7333-f632-4347-9787-2375f2f51b7b
-- title:
--   Rank Supermodular Covolume: covol eq rel Index mul covol
-- statement:
--   The Rank Supermodular Covolume construction uses the covol eq rel Index mul covol property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/DegSupermodZ.lean#L63-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/DegSupermodZ.lean#L63-L113

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermodZ
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
open Formalism Formalism.RankSupermodularCovolume
open Formalism.F
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem Formalism.RankSupermodularCovolume.covol_eq_relIndex_mul_covol (N N' : Submodule ℤ E) [DiscreteTopology N'] (hle : N ≤ N')
    (hrk : rk N = rk N') :
    covol N = (N.toAddSubgroup.relIndex N'.toAddSubgroup : ℝ) * covol N' := by sorry
