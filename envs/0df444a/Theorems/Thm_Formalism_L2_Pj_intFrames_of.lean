-- Prove2me | Theorems.Thm_Formalism_L2_Pj_intFrames_of
-- name    : Formalism.L2.Pj.intFrames_of
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:43:05.670856+00:00
-- url     : https://prove2.me/theorems/3e3a5324-07df-4be1-96a5-06559ea0b075
-- title:
--   Pj: int Frames of
-- statement:
--   The Pj construction uses the int Frames of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/IntFrames.lean#L91-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/IntFrames.lean#L91-L129

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_VAtVNeBot
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntFrames
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
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)
set_option maxHeartbeats 1000000

theorem Formalism.L2.Pj.intFrames_of (hC : ReciprocityTheory.ChartRestriction.G.Out.CubePullSt) (hG : GenFibreSt Xo c) (hL : LieFreeSt Xo c)
    (hT : ThetaFrameSt Xo c) (hS : SpreadSt Xo c) : IntFramesSt Xo c := by sorry
