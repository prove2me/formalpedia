-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_Sys_ordGE_alt
-- name    : Formalism.L2.FormalSeriesBounds.Sys.ordGE_alt
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:24:17.287577+00:00
-- url     : https://prove2.me/theorems/4061a19a-3d5b-5a3d-b408-51ae294a521b
-- title:
--   Sys: ord GE alt
-- statement:
--   The Sys construction uses the ord GE alt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LemmaMLin.lean#L412-L413
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LemmaMLin.lean#L412-L413

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_FrobeniusBaseCase_BaseCaseFalseGeneral
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LemmaMLin
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
open MvPowerSeries
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.BaseCaseIdentities (OrdGE NoConst)
variable {C : Type} [Field C] {V : VF C} {d : ℕ} {I J : Type} [Fintype I] [Fintype J]
  {Xc : Cart V d I J} (S : Sys Xc)

theorem Formalism.L2.FormalSeriesBounds.Sys.ordGE_alt {t : I → MvPowerSeries I C} (ht : S.IsT t) (c : I) : OrdGE 1 (t c) := by sorry
