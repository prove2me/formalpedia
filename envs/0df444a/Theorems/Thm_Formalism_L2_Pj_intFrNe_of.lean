-- Prove2me | Theorems.Thm_Formalism_L2_Pj_intFrNe_of
-- name    : Formalism.L2.Pj.intFrNe_of
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:58:47.003495+00:00
-- url     : https://prove2.me/theorems/aa14c88d-8a18-4058-a039-c0013a105f0c
-- title:
--   Pj: int Fr Ne of
-- statement:
--   The Pj construction uses the int Fr Ne of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CoreProofs.lean#L67-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CoreProofs.lean#L67-L76

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_VAtVNeBot
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CoreProofs
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

theorem Formalism.L2.Pj.intFrNe_of (hA : AlgPtLa Xo c) (hE : IntFrExt Xo c) :
    IntFrNe Xo c (fun _ _ y => IntFr.IsAlg y) := by sorry
