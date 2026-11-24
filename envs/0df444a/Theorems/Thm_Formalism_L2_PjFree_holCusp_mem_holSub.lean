-- Prove2me | Theorems.Thm_Formalism_L2_PjFree_holCusp_mem_holSub
-- name    : Formalism.L2.PjFree.holCusp_mem_holSub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T03:58:02.731343+00:00
-- url     : https://prove2.me/theorems/87ed5cf6-0390-4ed1-b1b8-b3aadd0230c1
-- title:
--   Pj Free: hol Cusp mem hol Sub
-- statement:
--   The Pj Free construction uses the hol Cusp mem hol Sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/JFDFree.lean#L45-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/JFDFree.lean#L45-L47

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

theorem Formalism.L2.PjFree.holCusp_mem_holSub (X : Comp → Data E r) (la : ∀ c, Wt (X c).Ψ r) {P : FDSec X}
    (h : IsHolCusp X la P) : P ∈ holSub X la := by sorry
