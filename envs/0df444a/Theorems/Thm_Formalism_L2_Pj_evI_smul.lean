-- Prove2me | Theorems.Thm_Formalism_L2_Pj_evI_smul
-- name    : Formalism.L2.Pj.evI_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:48:25.322994+00:00
-- url     : https://prove2.me/theorems/ccb79e28-9d65-4ed9-b041-ee53b6b2bb5c
-- title:
--   Pj: ev I smul
-- statement:
--   The Pj construction uses the ev I smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/VAtVNeBot.lean#L94-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/VAtVNeBot.lean#L94-L97

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsCombAt
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_OneLtAbsNormReal
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_VAtVNeBot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)
variable {Xo c}
variable (Xo c)
variable {Xo c}

theorem Formalism.L2.Pj.evI_smul {T : CDVR} {io : c.F →+* T.Fr} (y : IntFr Xo c T io) (a : c.F) (f : Rul Xo c) :
    evI y (a • f) = io a * evI y f := by sorry
