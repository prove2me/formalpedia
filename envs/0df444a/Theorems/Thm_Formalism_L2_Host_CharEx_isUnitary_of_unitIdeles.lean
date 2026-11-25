-- Prove2me | Theorems.Thm_Formalism_L2_Host_CharEx_isUnitary_of_unitIdeles
-- name    : Formalism.L2.Host.CharEx.isUnitary_of_unitIdeles
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T21:59:58.093881+00:00
-- url     : https://prove2.me/theorems/c4d956fc-2332-41bd-84a5-b2b0123b01ff
-- title:
--   Char Ex: is Unitary of unit Ideles
-- statement:
--   The Char Ex construction uses the is Unitary of unit Ideles property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/UnitaryNorms/CharExGen.lean#L97-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/UnitaryNorms/CharExGen.lean#L97-L103

import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_CharExGen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open Formalism Formalism.L2 Formalism.L2.Host
open Formalism.L2.Host.CharEx
variable (L : Type) [Field L] [NumberField L]
variable {L}

theorem Formalism.L2.Host.CharEx.isUnitary_of_unitIdeles (χ : HChar L) (h : ∀ u ∈ unitIdeles L, ‖((χ.1 u : ℂˣ) : ℂ)‖ = 1) : χ.IsUnitary := by sorry
