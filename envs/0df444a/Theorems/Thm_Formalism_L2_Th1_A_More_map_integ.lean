-- Prove2me | Theorems.Thm_Formalism_L2_Th1_A_More_map_integ
-- name    : Formalism.L2.Th1.A.More.map_integ
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T02:27:58.273099+00:00
-- url     : https://prove2.me/theorems/66d65c9c-c57d-5b82-98f2-4100e146a3e7
-- title:
--   More: map integ
-- statement:
--   The More construction uses the map integ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/ChainRuleFormalGroupVar.lean#L176-L179
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/ChainRuleFormalGroupVar.lean#L176-L179

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementM
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FglInvariant
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_ChainRuleFormalGroupVar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u v
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
open More
open Formalism.L2.Th1.A.More
variable {K : Type u} {L : Type v} [Field K] [Field L] (φ : K →+* L)

theorem Formalism.L2.Th1.A.More.map_integ (f : K⟦X⟧) : PowerSeries.map φ (integ f) = integ (PowerSeries.map φ f) := by sorry
