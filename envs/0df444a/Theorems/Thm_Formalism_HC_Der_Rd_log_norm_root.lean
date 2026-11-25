-- Prove2me | Theorems.Thm_Formalism_HC_Der_Rd_log_norm_root
-- name    : Formalism.HC.Der.Rd.log_norm_root
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:36:12.904463+00:00
-- url     : https://prove2.me/theorems/ba234f86-5a6f-4b8a-a6e7-6574bd1bc994
-- title:
--   Rd: log norm root
-- statement:
--   The Rd construction uses the log norm root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/RdDiff.lean#L75-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/RdDiff.lean#L75-L78

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RdDiff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Polynomial ArithmeticFunction
noncomputable section
open Formalism Formalism.HC Formalism.HC.Der Formalism.HC.Der.Rd

theorem Formalism.HC.Der.Rd.log_norm_root {m : ℕ} (hm : 1 < m) {L : Type*} [Field L] [NumberField L] {η : L}
    (hη : IsPrimitiveRoot η m) :
    Real.log |((Algebra.norm ℚ (η - 1) : ℚ) : ℝ)| * (m.totient : ℝ) = (Module.finrank ℚ L : ℝ) * vonMangoldt m := by sorry
