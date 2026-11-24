-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_Contr_coeff_iterate_zero
-- name    : Formalism.L2.FormalSeriesBounds.Contr.coeff_iterate_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:57:38.825133+00:00
-- url     : https://prove2.me/theorems/bb69197d-22c6-4110-a192-34110ad9bc04
-- title:
--   Contr: coeff iterate zero
-- statement:
--   The Contr construction uses the coeff iterate zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/CoeffIterateZero.lean#L55-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/CoeffIterateZero.lean#L55-L63

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_HasUniqueFixedPoint
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_coeff_iterate_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open MvPowerSeries
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.BaseCaseIdentities (OrdGE NoConst)
variable {k : Type*} [Field k] {Z B : Type*}
open Formalism.L2.FormalSeriesBounds.Contr
variable {Ψ : (B → MvPowerSeries Z k) → (B → MvPowerSeries Z k)} (H : Contr Ψ)
include H

theorem Formalism.L2.FormalSeriesBounds.Contr.coeff_iterate_zero (c : B) (A : Z →₀ ℕ) {n : ℕ} (hn : A.degree ≤ n) :
    coeff A (Ψ^[n] 0 c) = coeff A (H.fixPt c) := by sorry
