-- Prove2me | Theorems.Thm_Formalism_UnitaryBoundIntegral_ubint_mvExp_sum
-- name    : Formalism.UnitaryBoundIntegral.ubint_mvExp_sum
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T01:12:10.64157+00:00
-- url     : https://prove2.me/theorems/1d34c08e-448c-4eb4-87f1-24c439ee49e7
-- title:
--   Unitary Bound Integral: ubint mv Exp sum
-- statement:
--   The Unitary Bound Integral construction uses the ubint mv Exp sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DropLevelBounds/ConstantCoeffVanishing/UbintConstantCoeffEqZero.lean#L28-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DropLevelBounds/ConstantCoeffVanishing/UbintConstantCoeffEqZero.lean#L28-L40

import Mathlib
import Definitions.Def_Formalism_DropLevelBounds_Statement
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_ThmPExp
import Definitions.Def_Formalism_DropLevelBounds_ConstantCoeffVanishing_UbintConstantCoeffEqZero
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
open MvPowerSeries Finset
open Formalism Formalism.UnitaryBoundIntegral
open Formalism.IncomingBounds
variable {C : Type} [Field C] {σ : Type}

theorem Formalism.UnitaryBoundIntegral.ubint_mvExp_sum [CharZero C] {ι : Type} (s : Finset ι) (f : ι → MvPowerSeries σ C)
    (hf : ∀ i ∈ s, constantCoeff (f i) = 0) :
    mvExp (∑ i ∈ s, f i) = ∏ i ∈ s, mvExp (f i) := by sorry
