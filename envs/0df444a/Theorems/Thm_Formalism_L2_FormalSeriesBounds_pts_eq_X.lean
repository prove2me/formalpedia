-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_pts_eq_X
-- name    : Formalism.L2.FormalSeriesBounds.pts_eq_X
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:47:16.741724+00:00
-- url     : https://prove2.me/theorems/0018cafe-00d2-4959-a0cc-7a54571cce0a
-- title:
--   Formal Series Bounds: pts eq X
-- statement:
--   The Formal Series Bounds construction uses the pts eq X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieCartAdd.lean#L158-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieCartAdd.lean#L158-L161

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartAdd
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
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {C : Type} [Field C]
variable {dd : ℕ}

theorem Formalism.L2.FormalSeriesBounds.pts_eq_X : (fun p : Fin 2 × Fin dd => ![pt C (n := 2) dd 0, pt C (n := 2) dd 1] p.1 p.2) = MvPowerSeries.X := by sorry
