-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_InL_smul
-- name    : Formalism.L2.FormalSeriesBounds.InL.smul
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:24:15.665799+00:00
-- url     : https://prove2.me/theorems/41eab0d7-78d0-48db-852a-aff7ea3dce02
-- title:
--   In L: smul
-- statement:
--   The In L construction uses the smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/GeOfPowEqOne.lean#L48-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/GeOfPowEqOne.lean#L48-L49

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_GeOfPowEqOne
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_smul

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
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {C : Type} [Field C]

theorem Formalism.L2.FormalSeriesBounds.InL.smul {l : ℕ} {f : PowerSeries C} (hf : InL l f) (c : C) : InL l (c • f) := by sorry
