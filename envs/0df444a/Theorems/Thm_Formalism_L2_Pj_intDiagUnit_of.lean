-- Prove2me | Theorems.Thm_Formalism_L2_Pj_intDiagUnit_of
-- name    : Formalism.L2.Pj.intDiagUnit_of
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:57:45.783788+00:00
-- url     : https://prove2.me/theorems/77473227-3d35-4bea-9c5b-8da8544cc142
-- title:
--   Pj: int Diag Unit of
-- statement:
--   The Pj construction uses the int Diag Unit of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/FrameProofs.lean#L65-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/FrameProofs.lean#L65-L92

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

theorem Formalism.L2.Pj.intDiagUnit_of (hL : IntLatU Xo c) : IntDiagUnit Xo c := by sorry
