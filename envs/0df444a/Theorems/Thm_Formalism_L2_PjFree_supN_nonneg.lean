-- Prove2me | Theorems.Thm_Formalism_L2_PjFree_supN_nonneg
-- name    : Formalism.L2.PjFree.supN_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:38:21.199119+00:00
-- url     : https://prove2.me/theorems/84afa7da-e652-4549-812e-a78c06a4c1b9
-- title:
--   Pj Free: sup N nonneg
-- statement:
--   The Pj Free construction uses the sup N nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/JFDFree.lean#L49-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/JFDFree.lean#L49-L50

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

theorem Formalism.L2.PjFree.supN_nonneg (X : Comp → Data E r) (la : ∀ c, Wt (X c).Ψ r) (P : FDSec X) : 0 ≤ supN X la P := by sorry
