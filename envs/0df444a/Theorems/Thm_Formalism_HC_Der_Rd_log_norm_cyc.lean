-- Prove2me | Theorems.Thm_Formalism_HC_Der_Rd_log_norm_cyc
-- name    : Formalism.HC.Der.Rd.log_norm_cyc
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:36:20.309803+00:00
-- url     : https://prove2.me/theorems/7d1b88e0-5c71-4a13-a9a9-9bc21a5b429c
-- title:
--   Rd: log norm cyc
-- statement:
--   The Rd construction uses the log norm cyc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/RdDiff.lean#L60-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/RdDiff.lean#L60-L66

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

theorem Formalism.HC.Der.Rd.log_norm_cyc {m : ℕ} (hm : 1 < m) {F : Type*} [Field F] [NumberField F] [IsCyclotomicExtension {m} ℚ F]
    {η : F} (hη : IsPrimitiveRoot η m) : Real.log |((Algebra.norm ℚ (η - 1) : ℚ) : ℝ)| = vonMangoldt m := by sorry
