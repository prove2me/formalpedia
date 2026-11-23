-- Prove2me | Theorems.Thm_Formalism_L2_PjFree_epsPt_left
-- name    : Formalism.L2.PjFree.epsPt_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:46:21.280829+00:00
-- url     : https://prove2.me/theorems/8cc562a9-12bb-42a8-9eab-ccfc79be5aa2
-- title:
--   Pj Free: eps Pt left
-- statement:
--   The Pj Free construction uses the eps Pt left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/IntAllProofFree.lean#L156-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/IntAllProofFree.lean#L156-L159

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CoreProofs
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntAllFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ExistsOfValILeOne
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntAllProofFree
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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open scoped WithZero
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

theorem Formalism.L2.PjFree.epsPt_left {S : Type} [CommRing S] {Xo : Moduli Dw l} {x : Sp S ⟶ Xo.X}
    {v : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (hv : IsTanAt x v) (a : S) :
    (epsPt hv a).left = spMap (epsMul a) ≫ v := by sorry
