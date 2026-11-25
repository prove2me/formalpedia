-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_eqA
-- name    : Formalism.L2.FormalSeriesBounds.VP.eqA
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T08:15:19.920373+00:00
-- url     : https://prove2.me/theorems/a45ded4d-a055-487c-b8f4-2c453290e3b5
-- title:
--   VP: eq A
-- statement:
--   The VP construction uses the eq A property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ValuationEqPairOfUnitGerm.lean#L142-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ValuationEqPairOfUnitGerm.lean#L142-L181

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_PullbackLogCoordsEvalZero
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ValuationEqPairOfUnitGerm
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
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open Formalism.L2.FormalSeriesBounds.VP
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
variable (Y : FBChart C V O dd)

theorem Formalism.L2.FormalSeriesBounds.VP.eqA (m i : Fin dd) :
    ∑ k, MvPowerSeries.subst (exZero Y) (MvPowerSeries.pderiv C ((1 : Fin 2), i) (Y.B.G.F k)) * J Y m k =
      if m = i then 1 else 0 := by sorry
