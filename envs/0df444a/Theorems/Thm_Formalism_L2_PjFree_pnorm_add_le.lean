-- Prove2me | Theorems.Thm_Formalism_L2_PjFree_pnorm_add_le
-- name    : Formalism.L2.PjFree.pnorm_add_le
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:46:32.092369+00:00
-- url     : https://prove2.me/theorems/511ec24a-28cf-4640-b12c-c241608775e5
-- title:
--   Pj Free: pnorm add le
-- statement:
--   The Pj Free construction uses the pnorm add le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/JFDFree.lean#L28-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/JFDFree.lean#L28-L32

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

theorem Formalism.L2.PjFree.pnorm_add_le (X : Data E r) (la : Wt X.Ψ r) (P Q : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) :
    X.pnorm la (P + Q) x ≤ X.pnorm la P x + X.pnorm la Q x := by sorry
