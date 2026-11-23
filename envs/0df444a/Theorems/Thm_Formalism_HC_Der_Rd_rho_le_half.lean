-- Prove2me | Theorems.Thm_Formalism_HC_Der_Rd_rho_le_half
-- name    : Formalism.HC.Der.Rd.rho_le_half
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:12:51.815226+00:00
-- url     : https://prove2.me/theorems/0a8c63a7-cfee-4d68-a1d8-5ada2c53f702
-- title:
--   Rd: rho le half
-- statement:
--   The Rd construction uses the rho le half property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/RdArith.lean#L346-L390
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/RdArith.lean#L346-L390

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

theorem Formalism.HC.Der.Rd.rho_le_half (U : Subgroup (ZMod N)ˣ) {f : ℕ} (hf : f ∣ N)
    (h : ∀ u ∈ KK N f, ∀ v ∈ KK N f, u ∉ U → v ∉ U → u * v ∈ U) : rho U f ≤ 1 / 2 := by sorry
