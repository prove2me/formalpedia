-- Prove2me | Theorems.Thm_Formalism_REAL_bool_trichotomy_of_ne
-- name    : Formalism.REAL.bool_trichotomy_of_ne
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T10:20:35.730812+00:00
-- url     : https://prove2.me/theorems/c1f39ac2-d83c-4fdd-9d03-1fa6e1d50058
-- title:
--   REAL: bool trichotomy of ne
-- statement:
--   The REAL construction uses the bool trichotomy of ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/NoncompactArrFiniteDimensional.lean#L339-L339
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/NoncompactArrFiniteDimensional.lean#L339-L339

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_NoncompactArrFiniteDimensional
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Finset
noncomputable section
open Formalism Formalism.REAL
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}

theorem Formalism.REAL.bool_trichotomy_of_ne : ∀ x y z : Bool, x ≠ y → (z = x ∧ z ≠ y) ∨ (z = y ∧ z ≠ x) := by sorry
