-- Prove2me | Theorems.Thm_Formalism_G0_TopsWeightFunctionBounds_mod_inj
-- name    : Formalism.G0.TopsWeightFunctionBounds.mod_inj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:11:40.255747+00:00
-- url     : https://prove2.me/theorems/34273019-ae86-4f27-b3e7-8fbdddee0a96
-- title:
--   Tops Weight Function Bounds: mod inj
-- statement:
--   The Tops Weight Function Bounds construction uses the mod inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TopsChoicePartB.lean#L431-L433
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TopsChoicePartB.lean#L431-L433

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
noncomputable section
open scoped BigOperators
open Formalism Formalism.G0 Formalism.G0.TopsWeightFunctionBounds
variable {R L₂ : ℕ} {δ : ℝ}

theorem Formalism.G0.TopsWeightFunctionBounds.mod_inj {n i x y : ℕ} (hx : x < n) (hy : y < n) (h : (i + x) % n = (i + y) % n) : x = y := by sorry
