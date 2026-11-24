-- Prove2me | Theorems.Thm_Formalism_L2_Host_CharEx_norm_pow_eq_one
-- name    : Formalism.L2.Host.CharEx.norm_pow_eq_one
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T21:54:10.964828+00:00
-- url     : https://prove2.me/theorems/4ff97983-4898-440d-ae4e-7110b704458f
-- title:
--   Char Ex: norm pow eq one
-- statement:
--   The Char Ex construction uses the norm pow eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/UnitaryNorms/CharExGen.lean#L93-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/UnitaryNorms/CharExGen.lean#L93-L95

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

theorem Formalism.L2.Host.CharEx.norm_pow_eq_one {z : ℂˣ} {h : ℕ} (hh : 0 < h) (hz : ‖((z ^ h : ℂˣ) : ℂ)‖ = 1) : ‖(z : ℂ)‖ = 1 := by sorry
