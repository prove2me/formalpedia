-- Prove2me | Theorems.Thm_Formalism_L2_Pj_CompSplitPfD_cspD_local
-- name    : Formalism.L2.Pj.CompSplitPfD.cspD_local
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:46:13.003075+00:00
-- url     : https://prove2.me/theorems/6399f3ae-7e92-460c-85d0-7924b80e7759
-- title:
--   Comp Split Pf D: csp D local
-- statement:
--   The Comp Split Pf D construction uses the csp D local property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CompSplitPfD.lean#L64-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CompSplitPfD.lean#L64-L104

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

theorem Formalism.L2.Pj.CompSplitPfD.cspD_local (Xo : Moduli Dw l) (c : Coeff l) (x : Xo.XF c) :
    ∃ (Y : Type) (_ : TopologicalSpace Y) (g : Y → Xo.XF c), IsOpenEmbedding g ∧ x ∈ Set.range g ∧
      ∀ a b y : Y, (∀ a', a' ⤳ a → a' = a) → (∀ b', b' ⤳ b → b' = b) → a ⤳ y → b ⤳ y → a = b := by sorry
