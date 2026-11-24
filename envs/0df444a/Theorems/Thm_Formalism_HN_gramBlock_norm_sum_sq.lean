-- Prove2me | Theorems.Thm_Formalism_HN_gramBlock_norm_sum_sq
-- name    : Formalism.HN.gramBlock_norm_sum_sq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:28:55.928878+00:00
-- url     : https://prove2.me/theorems/7bb008eb-6d38-423c-bd58-f1586a18b4ce
-- title:
--   HN: gram Block norm sum sq
-- statement:
--   The HN construction uses the gram Block norm sum sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/GramBlock.lean#L10-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/GramBlock.lean#L10-L18

import Definitions.Def_Formalism_HarderNarasimhan_DefsPl
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_GramBlock
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
noncomputable section
open Formalism Formalism.HN

theorem Formalism.HN.gramBlock_norm_sum_sq {P F : Type*} [Fintype P] [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] (y : P → F) (h : ∀ v w, v ≠ w → inner ℝ (y v) (y w) = 0) :
    ‖∑ v, y v‖ ^ 2 = ∑ v, ‖y v‖ ^ 2 := by sorry
