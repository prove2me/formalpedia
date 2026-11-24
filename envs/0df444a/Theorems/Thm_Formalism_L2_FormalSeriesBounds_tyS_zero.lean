-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_tyS_zero
-- name    : Formalism.L2.FormalSeriesBounds.tyS_zero
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T11:20:27.490082+00:00
-- url     : https://prove2.me/theorems/4d48334a-1633-4e5b-9aa6-ba0cbbaa589b
-- title:
--   Formal Series Bounds: ty S zero
-- statement:
--   The Formal Series Bounds construction uses the ty S zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ConstMemTypeSetOfNonneg.lean#L45-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ConstMemTypeSetOfNonneg.lean#L45-L48

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieAxes
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ConstMemTypeSetOfNonneg
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
variable {l : ℕ} (hl : 2 ≤ l)
include hl
omit hl

theorem Formalism.L2.FormalSeriesBounds.tyS_zero : tyS l (fun _ => (0 : C)) = 0 := by sorry
