-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_ThickExists_coeff_zero
-- name    : Formalism.FrobeniusOrbits.ThickExists.coeff_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:56:09.983202+00:00
-- url     : https://prove2.me/theorems/75aaba7e-c77a-4878-90e4-9f0d807f95c8
-- title:
--   Thick Exists: coeff zero
-- statement:
--   The Thick Exists construction uses the coeff zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/ThickExists.lean#L11-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/ThickExists.lean#L11-L13

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_HostThickExists
import Definitions.Def_Lemmata_GeneralBFactSecondLast_Imports
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ThickExists
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.FrobeniusOrbits Formalism.FrobeniusOrbits.ThickExists

theorem Formalism.FrobeniusOrbits.ThickExists.coeff_zero (B : ℤ) : ∀ {S : ℕ} (c : Fin S → ℤ), (∀ m, |c m| < B) →
    ∑ m, c m * B ^ (m : ℕ) = 0 → ∀ m, c m = 0 := by sorry
