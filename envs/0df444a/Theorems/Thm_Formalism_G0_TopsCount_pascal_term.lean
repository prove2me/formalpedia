-- Prove2me | Theorems.Thm_Formalism_G0_TopsCount_pascal_term
-- name    : Formalism.G0.TopsCount.pascal_term
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:11:32.925824+00:00
-- url     : https://prove2.me/theorems/b420d865-ffa9-4a30-a33a-be75f264e83a
-- title:
--   Tops Count: pascal term
-- statement:
--   The Tops Count construction uses the pascal term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TopsChoiceCount.lean#L24-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TopsChoiceCount.lean#L24-L35

import Definitions.Def_Formalism_SubspaceCounting_TopsChoiceSecondBound
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TopsChoiceCount
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.G0
open Formalism.G0.TopsCount

theorem Formalism.G0.TopsCount.pascal_term (m k : ℕ) (δ : ℝ) :
    ((m + 1).choose (k + 1) : ℝ) * δ ^ (k + 1) * (1 - δ) ^ (m + 1 - (k + 1)) =
      (1 - δ) * a m δ (k + 1) + δ * a m δ k := by sorry
