-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_tyS_Vpow
-- name    : Formalism.L2.FormalSeriesBounds.tyS_Vpow
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T00:25:01.726036+00:00
-- url     : https://prove2.me/theorems/c33bd825-7cd6-4242-8150-8134551df91a
-- title:
--   Formal Series Bounds: ty S Vpow
-- statement:
--   The Formal Series Bounds construction uses the ty S Vpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/GeOfPowEqOne.lean#L81-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/GeOfPowEqOne.lean#L81-L114

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_GeOfPowEqOne
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

theorem Formalism.L2.FormalSeriesBounds.tyS_Vpow {l : ℕ} (hl : 2 ≤ l) (a : ℕ → C) :
    tyS l (fun s => if s < 1 then 0 else a (s - 1)) =
      PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ l) (tyS l a) := by sorry
