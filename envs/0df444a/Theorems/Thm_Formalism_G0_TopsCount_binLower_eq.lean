-- Prove2me | Theorems.Thm_Formalism_G0_TopsCount_binLower_eq
-- name    : Formalism.G0.TopsCount.binLower_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:11:25.45039+00:00
-- url     : https://prove2.me/theorems/853175de-4cb7-4d98-82ea-cbcfe992efb2
-- title:
--   Tops Count: bin Lower eq
-- statement:
--   The Tops Count construction uses the bin Lower eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TopsChoiceCount.lean#L37-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TopsChoiceCount.lean#L37-L53

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

theorem Formalism.G0.TopsCount.binLower_eq (m : ℕ) (δ : ℝ) (N : ℕ) :
    binLower (m + 1) δ N = (1 - δ) * A m δ N + δ * A m δ (N - 1) := by sorry
