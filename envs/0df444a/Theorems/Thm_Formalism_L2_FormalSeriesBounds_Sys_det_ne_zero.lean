-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_Sys_det_ne_zero
-- name    : Formalism.L2.FormalSeriesBounds.Sys.det_ne_zero
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:26:12.216495+00:00
-- url     : https://prove2.me/theorems/af94161a-14df-5009-ba7c-b5bc057321bb
-- title:
--   Sys: det ne zero
-- statement:
--   The Sys construction uses the det ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LemmaMLin.lean#L403-L410
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LemmaMLin.lean#L403-L410

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

theorem Formalism.L2.FormalSeriesBounds.Sys.det_ne_zero : (Matrix.of fun c k : I => S.al c 0 k).det ≠ 0 := by sorry
