-- Prove2me | Theorems.Thm_Formalism_L2_Pj_wtField_of
-- name    : Formalism.L2.Pj.wtField_of
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:41:13.942662+00:00
-- url     : https://prove2.me/theorems/df7ec114-928b-4edc-95e4-9678efe28a33
-- title:
--   Pj: wt Field of
-- statement:
--   The Pj construction uses the wt Field of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/FrameProofs.lean#L44-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/FrameProofs.lean#L44-L56

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CoreProofs
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FrameProofs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}

theorem Formalism.L2.Pj.wtField_of (hD : BorDesc Xo c) : WtField Xo c := by sorry
