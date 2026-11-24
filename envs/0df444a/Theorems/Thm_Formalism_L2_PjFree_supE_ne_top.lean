-- Prove2me | Theorems.Thm_Formalism_L2_PjFree_supE_ne_top
-- name    : Formalism.L2.PjFree.supE_ne_top
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:38:26.513551+00:00
-- url     : https://prove2.me/theorems/c457edf9-1c2d-40f7-a9fc-6602d316591a
-- title:
--   Pj Free: sup E ne top
-- statement:
--   The Pj Free construction uses the sup E ne top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/NormsFree.lean#L40-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/NormsFree.lean#L40-L61

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CuspFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RulInst
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PtFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_NormsFree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.PjFree
open Formalism.L2.Pj
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Comp : Type}
  (X : Comp → Data E r) (la : ∀ c, ReciprocityTheory.ChartRestriction.G.FD.Wt (X c).Ψ r)

theorem Formalism.L2.PjFree.supE_ne_top [Fintype Comp] {P : FDSec X} (h : P ∈ holSub X la) : supE X la P ≠ ⊤ := by sorry
