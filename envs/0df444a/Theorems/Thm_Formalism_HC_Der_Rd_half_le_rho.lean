-- Prove2me | Theorems.Thm_Formalism_HC_Der_Rd_half_le_rho
-- name    : Formalism.HC.Der.Rd.half_le_rho
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:12:50.690311+00:00
-- url     : https://prove2.me/theorems/55d4e958-ee37-4b4f-b5e4-65f728dc97ab
-- title:
--   Rd: half le rho
-- statement:
--   The Rd construction uses the half le rho property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/RdArith.lean#L302-L344
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/RdArith.lean#L302-L344

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

theorem Formalism.HC.Der.Rd.half_le_rho (U : Subgroup (ZMod N)ˣ) {f : ℕ} (hf : f ∣ N) (h : ∃ u ∈ KK N f, u ∉ U) : 1 / 2 ≤ rho U f := by sorry
