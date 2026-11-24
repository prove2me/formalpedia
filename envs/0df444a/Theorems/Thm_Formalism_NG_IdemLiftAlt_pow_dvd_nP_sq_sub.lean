-- Prove2me | Theorems.Thm_Formalism_NG_IdemLiftAlt_pow_dvd_nP_sq_sub
-- name    : Formalism.NG.IdemLiftAlt.pow_dvd_nP_sq_sub
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T10:14:46.486002+00:00
-- url     : https://prove2.me/theorems/e3281017-30c1-4df7-87c5-4673b90f5a7e
-- title:
--   Idem Lift Alt: pow dvd n P sq sub
-- statement:
--   The Idem Lift Alt construction uses the pow dvd n P sq sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/SpacedProductLowerBound.lean#L15-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/SpacedProductLowerBound.lean#L15-L24

import Definitions.Def_Formalism_CharacterColumnKernels_StatOntoLattice
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_SpacedProductLowerBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open Formalism Formalism.NG
open Formalism.NG.IdemLiftAlt

theorem Formalism.NG.IdemLiftAlt.pow_dvd_nP_sq_sub (k : ℕ) : ∃ U : ℤ[X], nP k ^ 2 - nP k = (X ^ 2 - X) ^ (2 ^ k) * U := by sorry
