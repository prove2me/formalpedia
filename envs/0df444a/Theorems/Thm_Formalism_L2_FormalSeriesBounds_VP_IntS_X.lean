-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_IntS_X
-- name    : Formalism.L2.FormalSeriesBounds.VP.IntS_X
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T07:17:32.097849+00:00
-- url     : https://prove2.me/theorems/abeb2c10-ece4-4e7f-b179-931a901174fb
-- title:
--   VP: Int S X
-- statement:
--   The VP construction uses the Int S X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/IntSProd.lean#L79-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/IntSProd.lean#L79-L84

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ConstantCoeffSinglePointZero
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_IntSProd
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X

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
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open Formalism.L2.FormalSeriesBounds.VP
variable {C : Type} [Field C] {V : VF C} {σ : Type}

theorem Formalism.L2.FormalSeriesBounds.VP.IntS_X (s : σ) : IntS V (MvPowerSeries.X s : MvPowerSeries σ C) := by sorry
