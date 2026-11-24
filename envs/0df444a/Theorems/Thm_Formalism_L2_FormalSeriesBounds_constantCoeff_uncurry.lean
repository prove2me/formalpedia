-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_constantCoeff_uncurry
-- name    : Formalism.L2.FormalSeriesBounds.constantCoeff_uncurry
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:07:02.735409+00:00
-- url     : https://prove2.me/theorems/7280d0e1-6280-4a89-b169-c969946c57b3
-- title:
--   Formal Series Bounds: constant Coeff uncurry
-- statement:
--   The Formal Series Bounds construction uses the constant Coeff uncurry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieAxes.lean#L162-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieAxes.lean#L162-L165

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieAxes
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
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ MvPowerSeries
variable {C : Type} [Field C]
variable {dd : ℕ}

theorem Formalism.L2.FormalSeriesBounds.constantCoeff_uncurry (f : PS C 1 dd) : constantCoeff (un1 f) = constantCoeff f := by sorry
