-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_RawChart_onLf_swap
-- name    : Formalism.L2.FormalSeriesBounds.RawChart.onLf_swap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:51:10.447798+00:00
-- url     : https://prove2.me/theorems/00190304-db20-45ee-a0d6-4c75bffde71f
-- title:
--   Raw Chart: on Lf swap
-- statement:
--   The Raw Chart construction uses the on Lf swap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieDefs.lean#L120-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieDefs.lean#L120-L123

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_IntSubst
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieDefs
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
open Formalism.IncomingBounds
variable {C : Type} [Field C]
open Formalism.L2.FormalSeriesBounds.RawChart
variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] (X : RawChart C d I κ)
variable {X}
variable (X)

theorem Formalism.L2.FormalSeriesBounds.RawChart.onLf_swap (a a' : ZMod d) (w : WV I) : X.OnLf 1 a' a w ↔ X.OnLf 0 a a' w := by sorry
