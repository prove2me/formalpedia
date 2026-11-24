-- Prove2me | Theorems.Thm_Formalism_L2_Pj_CompSplitPfD_cspD_smooth
-- name    : Formalism.L2.Pj.CompSplitPfD.cspD_smooth
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:54:56.497677+00:00
-- url     : https://prove2.me/theorems/5f7de1dd-bb61-47ce-869f-c2b12f6419cc
-- title:
--   Comp Split Pf D: csp D smooth
-- statement:
--   The Comp Split Pf D construction uses the csp D smooth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CompSplitPfD.lean#L57-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CompSplitPfD.lean#L57-L62

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
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

theorem Formalism.L2.Pj.CompSplitPfD.cspD_smooth (Xo : Moduli Dw l) (c : Coeff l) :
    Smooth (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) := by sorry
