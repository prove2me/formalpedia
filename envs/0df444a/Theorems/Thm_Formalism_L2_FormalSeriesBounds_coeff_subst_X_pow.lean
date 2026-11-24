-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_coeff_subst_X_pow
-- name    : Formalism.L2.FormalSeriesBounds.coeff_subst_X_pow
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T11:34:54.54407+00:00
-- url     : https://prove2.me/theorems/a48bd68d-ef63-4b1c-b4d8-b9acd63cda39
-- title:
--   Formal Series Bounds: coeff subst X pow
-- statement:
--   The Formal Series Bounds construction uses the coeff subst X pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ConstMemTypeSetOfNonneg.lean#L189-L196
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ConstMemTypeSetOfNonneg.lean#L189-L196

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieAxes
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ConstMemTypeSetOfNonneg
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst

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

theorem Formalism.L2.FormalSeriesBounds.coeff_subst_X_pow {l : ℕ} (hl : 0 < l) (f : PowerSeries C) (q : ℕ) :
    PowerSeries.coeff (l * q) (PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ l) f) = PowerSeries.coeff q f := by sorry
