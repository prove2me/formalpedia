-- Prove2me | Theorems.Thm_Formalism_G0_TopsCount_a_nonneg
-- name    : Formalism.G0.TopsCount.a_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:31:27.099371+00:00
-- url     : https://prove2.me/theorems/b6211f01-0561-4ba5-803d-c333b4a7f1d4
-- title:
--   Tops Count: a nonneg
-- statement:
--   The Tops Count construction uses the a nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TopsChoiceCount.lean#L16-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TopsChoiceCount.lean#L16-L19

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

theorem Formalism.G0.TopsCount.a_nonneg {m : ℕ} {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ ≤ 1) (j : ℕ) : 0 ≤ a m δ j := by sorry
