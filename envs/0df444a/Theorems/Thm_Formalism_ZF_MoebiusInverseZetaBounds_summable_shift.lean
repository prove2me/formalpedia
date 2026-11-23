-- Prove2me | Theorems.Thm_Formalism_ZF_MoebiusInverseZetaBounds_summable_shift
-- name    : Formalism.ZF.MoebiusInverseZetaBounds.summable_shift
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:36:09.899233+00:00
-- url     : https://prove2.me/theorems/62b790b8-db34-4bfe-a55a-18aac17592d1
-- title:
--   Moebius Inverse Zeta Bounds: summable shift
-- statement:
--   The Moebius Inverse Zeta Bounds construction uses the summable shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/ZetaInvBound.lean#L11-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/ZetaInvBound.lean#L11-L13

import Definitions.Def_Formalism_ZeroFreeRegion_SmallHeightLogDeriv
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_ZetaInvBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology LSeries ArithmeticFunction
noncomputable section
open Formalism Formalism.ZF
open Formalism.ZF.MoebiusInverseZetaBounds

theorem Formalism.ZF.MoebiusInverseZetaBounds.summable_shift {p : ℝ} (hp : p < -1) : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ p) := by sorry
