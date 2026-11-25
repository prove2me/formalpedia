-- Prove2me | Theorems.Thm_Formalism_L2_PjFree_pnorm_zero
-- name    : Formalism.L2.PjFree.pnorm_zero
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:46:18.317334+00:00
-- url     : https://prove2.me/theorems/11e19ef2-ae46-5bf8-9885-cffc0db5135c
-- title:
--   Pj Free: pnorm zero
-- statement:
--   The Pj Free construction uses the pnorm zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/JFDFree.lean#L39-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/JFDFree.lean#L39-L40

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ModerateCoefficientPositivity
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_JFDFree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField ReciprocityTheory.ChartRestriction.G.FD
open Formalism Formalism.L2 Formalism.L2.PjFree
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Comp : Type}

theorem Formalism.L2.PjFree.pnorm_zero (X : Data E r) (la : Wt X.Ψ r) (x : Frame X.Ψ r) : X.pnorm la 0 x = 0 := by sorry
