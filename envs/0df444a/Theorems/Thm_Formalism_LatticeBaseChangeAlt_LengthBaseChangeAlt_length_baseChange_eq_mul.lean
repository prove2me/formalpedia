-- Prove2me | Theorems.Thm_Formalism_LatticeBaseChangeAlt_LengthBaseChangeAlt_length_baseChange_eq_mul
-- name    : Formalism.LatticeBaseChangeAlt.LengthBaseChangeAlt.length_baseChange_eq_mul
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T09:51:48.897701+00:00
-- url     : https://prove2.me/theorems/25926801-739e-4223-b7ca-74b2f9eac2e1
-- title:
--   Length Base Change Alt: length base Change eq mul
-- statement:
--   The Length Base Change Alt construction uses the length base Change eq mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FilteredPoleLength/LocalDescentLevels/LengthBaseChange.lean#L12-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FilteredPoleLength/LocalDescentLevels/LengthBaseChange.lean#L12-L43

import Definitions.Def_Formalism_FilteredPoleLength_ReducedBasisBounds_LengthBaseChangeLocal
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_MemSpanBasisFun
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_LengthBaseChange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.LatticeBaseChangeAlt
open Module TensorProduct
open Formalism.LatticeBaseChangeAlt.LengthBaseChangeAlt

theorem Formalism.LatticeBaseChangeAlt.LengthBaseChangeAlt.length_baseChange_eq_mul {O O₁ : Type} [CommRing O] [CommRing O₁] [Algebra O O₁]
    [Module.Flat O O₁] (ε : ℕ∞)
    (hs : ∀ (S : Type) [AddCommGroup S] [Module O S], IsSimpleModule O S →
      Module.length O₁ (TensorProduct O O₁ S) = ε)
    (Q : Type) [AddCommGroup Q] [Module O Q] (h : IsFiniteLength O Q) :
    Module.length O₁ (TensorProduct O O₁ Q) = ε * Module.length O Q := by sorry
