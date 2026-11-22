-- Prove2me | Theorems.Thm_Formalism_G0_TopsWeightFunctionBounds_c_nonneg
-- name    : Formalism.G0.TopsWeightFunctionBounds.c_nonneg
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T18:25:18.327124+00:00
-- url     : https://prove2.me/theorems/3bcb00d0-f626-4fe2-9452-bde17dc86c38
-- title:
--   Tops Weight Function Bounds: c nonneg
-- statement:
--   The Tops Weight Function Bounds construction uses the c nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TopsChoicePartB.lean#L211-L212
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TopsChoicePartB.lean#L211-L212

import Definitions.Def_Formalism_SubspaceCounting_TopsChoiceSecondBound
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TopsChoicePartB
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
noncomputable section
open scoped BigOperators
open Formalism Formalism.G0 Formalism.G0.TopsWeightFunctionBounds
variable {R L₂ : ℕ} {δ : ℝ}

theorem Formalism.G0.TopsWeightFunctionBounds.c_nonneg (h0 : 0 ≤ δ) (hLδ : (L₂ : ℝ) * δ ≤ 1) : 0 ≤ 1 - aF L₂ δ ^ R := by sorry
