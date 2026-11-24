-- Prove2me | Theorems.Thm_Formalism_HC_Der_Rd_log_index_le
-- name    : Formalism.HC.Der.Rd.log_index_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:28:46.907054+00:00
-- url     : https://prove2.me/theorems/28e0cabd-fcf3-4a64-9fc7-0c6499c46acd
-- title:
--   Rd: log index le
-- statement:
--   The Rd construction uses the log index le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/RdBound.lean#L29-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/RdBound.lean#L29-L109

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RdArith
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RdBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ArithmeticFunction Finset
noncomputable section
open Formalism Formalism.HC Formalism.HC.Der Formalism.HC.Der.Rd
variable {N : ℕ} [NeZero N] (U : Subgroup (ZMod N)ˣ)

theorem Formalism.HC.Der.Rd.log_index_le : Real.log U.index ≤ 2 * SS U := by sorry
