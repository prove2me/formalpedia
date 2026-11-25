-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_coeff_dnL
-- name    : Formalism.L2.FormalSeriesBounds.coeff_dnL
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:31:01.601954+00:00
-- url     : https://prove2.me/theorems/2c4001c2-6c4d-44ee-8418-a19522bbd1e4
-- title:
--   Formal Series Bounds: coeff dn L
-- statement:
--   The Formal Series Bounds construction uses the coeff dn L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/GeOfPowEqOne.lean#L18-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/GeOfPowEqOne.lean#L18-L21

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_GeOfPowEqOne
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

theorem Formalism.L2.FormalSeriesBounds.coeff_dnL (l : ℕ) (f : PowerSeries C) (n : ℕ) :
    PowerSeries.coeff n (dnL l f) = PowerSeries.coeff (l * n) f := by sorry
