-- Prove2me | Theorems.Thm_Formalism_L2_Host_CharEx_mem_unitIdeles_iff
-- name    : Formalism.L2.Host.CharEx.mem_unitIdeles_iff
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T21:54:09.118643+00:00
-- url     : https://prove2.me/theorems/a65465ba-6fec-4f46-a19b-8da424bb52be
-- title:
--   Char Ex: mem unit Ideles iff
-- statement:
--   The Char Ex construction uses the mem unit Ideles iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/UnitaryNorms/CharExGen.lean#L24-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/UnitaryNorms/CharExGen.lean#L24-L26

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

theorem Formalism.L2.Host.CharEx.mem_unitIdeles_iff (u : Ideles L) : u ∈ unitIdeles L ↔ u ∈ rayUnits L ⊤ ∅ := by sorry
