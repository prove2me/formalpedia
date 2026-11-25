-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_linPull_prod
-- name    : Formalism.L2.FormalSeriesBounds.VP.linPull_prod
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:36:09.332084+00:00
-- url     : https://prove2.me/theorems/b351a57c-6254-53dd-83dc-09ac00105038
-- title:
--   VP: lin Pull prod
-- statement:
--   The VP construction uses the lin Pull prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieValG.lean#L33-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieValG.lean#L33-L36

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ValuationEqPairOfUnitGerm
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieValG
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
  {Var : Type} [Fintype Var] {n : ℕ}
variable (Y : FBChart C V O dd) (M : Var → Fin n × Fin dd → C)

theorem Formalism.L2.FormalSeriesBounds.VP.linPull_prod {ι : Type} (s : Finset ι) (F : ι → PS C n dd) :
    linPull Y M (∏ i ∈ s, F i) = ∏ i ∈ s, linPull Y M (F i) := by sorry
