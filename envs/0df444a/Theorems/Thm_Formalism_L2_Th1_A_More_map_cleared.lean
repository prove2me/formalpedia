-- Prove2me | Theorems.Thm_Formalism_L2_Th1_A_More_map_cleared
-- name    : Formalism.L2.Th1.A.More.map_cleared
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T02:13:40.039591+00:00
-- url     : https://prove2.me/theorems/88b89ab7-8200-5c9a-b412-d0638fae531b
-- title:
--   More: map cleared
-- statement:
--   The More construction uses the map cleared property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/ChainRuleFormalGroupVar.lean#L191-L195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/ChainRuleFormalGroupVar.lean#L191-L195

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

theorem Formalism.L2.Th1.A.More.map_cleared {g2 g3 : K} {r : K⟦X⟧} (h : WpSh.Cleared g2 g3 r) :
    WpSh.Cleared (φ g2) (φ g3) (PowerSeries.map φ r) := by sorry
