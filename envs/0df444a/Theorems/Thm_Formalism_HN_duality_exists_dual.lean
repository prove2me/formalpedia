-- Prove2me | Theorems.Thm_Formalism_HN_duality_exists_dual
-- name    : Formalism.HN.duality_exists_dual
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:28:15.407625+00:00
-- url     : https://prove2.me/theorems/cecb43b5-00e6-41b4-b2e7-161b969cc066
-- title:
--   HN: duality exists dual
-- statement:
--   The HN construction uses the duality exists dual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/Duality.lean#L109-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/Duality.lean#L109-L145

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

theorem Formalism.HN.duality_exists_dual (v : ι → E) (hv : LinearIndependent ℝ v) :
    ∃ w : ι → E, (∀ i, w i ∈ span ℝ (Set.range v)) ∧
      (∀ k i, inner ℝ (v k) (w i) = if k = i then 1 else 0) ∧
      (Matrix.gram ℝ w).det = ((Matrix.gram ℝ v).det)⁻¹ := by sorry
