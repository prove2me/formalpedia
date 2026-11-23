-- Prove2me | Theorems.Thm_Formalism_HC_Der_Rd_rho_nonneg
-- name    : Formalism.HC.Der.Rd.rho_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:07:45.118875+00:00
-- url     : https://prove2.me/theorems/07367255-ab1e-409c-b036-b07f853616c9
-- title:
--   Rd: rho nonneg
-- statement:
--   The Rd construction uses the rho nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/RdArith.lean#L243-L245
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/RdArith.lean#L243-L245

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RdArith
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
variable {N : ℕ} [NeZero N]

theorem Formalism.HC.Der.Rd.rho_nonneg (U : Subgroup (ZMod N)ˣ) (f : ℕ) : 0 ≤ rho U f := by sorry
