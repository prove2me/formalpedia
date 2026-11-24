-- Prove2me | Theorems.Thm_Formalism_L2_Pj_CompSplitPfD_cspD_gen
-- name    : Formalism.L2.Pj.CompSplitPfD.cspD_gen
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:40:16.010949+00:00
-- url     : https://prove2.me/theorems/48a12112-0dfa-4257-9c80-14320658c2c0
-- title:
--   Comp Split Pf D: csp D gen
-- statement:
--   The Comp Split Pf D construction uses the csp D gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CompSplitPfD.lean#L11-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CompSplitPfD.lean#L11-L14

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsGenFrGenFr
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CompFin
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CompSplitPfC
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CompSplitPfD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.CompSplitPfD
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Topology

theorem Formalism.L2.Pj.CompSplitPfD.cspD_gen {X : Type} [TopologicalSpace X] [QuasiSober X] {W : Set X} (hW : W ∈ irreducibleComponents X) :
    IsGenericPoint hW.1.genericPoint W := by sorry
