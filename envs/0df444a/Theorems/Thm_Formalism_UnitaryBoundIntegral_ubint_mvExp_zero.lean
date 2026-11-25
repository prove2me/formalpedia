-- Prove2me | Theorems.Thm_Formalism_UnitaryBoundIntegral_ubint_mvExp_zero
-- name    : Formalism.UnitaryBoundIntegral.ubint_mvExp_zero
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:37:44.238954+00:00
-- url     : https://prove2.me/theorems/b1e2db49-a024-46b4-8cd1-28bb06d35afe
-- title:
--   Unitary Bound Integral: ubint mv Exp zero
-- statement:
--   The Unitary Bound Integral construction uses the ubint mv Exp zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DropLevelBounds/ConstantCoeffVanishing/UbintConstantCoeffEqZero.lean#L17-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DropLevelBounds/ConstantCoeffVanishing/UbintConstantCoeffEqZero.lean#L17-L26

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

theorem Formalism.UnitaryBoundIntegral.ubint_mvExp_zero : mvExp (0 : MvPowerSeries σ C) = 1 := by sorry
