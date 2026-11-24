-- Prove2me | Theorems.Thm_Formalism_L2_Host_CharEx_exists_hchar_eq_on
-- name    : Formalism.L2.Host.CharEx.exists_hchar_eq_on
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T21:54:31.694838+00:00
-- url     : https://prove2.me/theorems/13c9b0c2-3222-4e97-a97f-f1b9269479df
-- title:
--   Char Ex: exists hchar eq on
-- statement:
--   The Char Ex construction uses the exists hchar eq on property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/UnitaryNorms/CharExGen.lean#L46-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/UnitaryNorms/CharExGen.lean#L46-L91

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

theorem Formalism.L2.Host.CharEx.exists_hchar_eq_on (hD : DivExtC) (hO : OpenUnits L) (M : Subgroup (Ideles L)) (hM : unitIdeles L ≤ M)
    (Φ : Ideles L →* ℂˣ) (hΦ : Continuous Φ) (h1 : ∀ k : Lˣ, diagUnits L k ∈ M → Φ (diagUnits L k) = 1) :
    ∃ χ : HChar L, ∀ m ∈ M, χ.1 m = Φ m := by sorry
