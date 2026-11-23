-- Prove2me | Theorems.Thm_Formalism_L2_G_ServJoint_vAdd_eq_vw
-- name    : Formalism.L2.G.ServJoint.vAdd_eq_vw
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:51:33.958613+00:00
-- url     : https://prove2.me/theorems/c5dc7ef6-e59d-4d7d-9314-6d3901a5637b
-- title:
--   Serv Joint: v Add eq vw
-- statement:
--   The Serv Joint construction uses the v Add eq vw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/JointServices/VAddEqVw.lean#L37-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/JointServices/VAddEqVw.lean#L37-L52

import Definitions.Def_Formalism_LocalRingCardinality_DataArith
import Definitions.Def_Formalism_LocalToGlobal_ExponentGrids_ExponentGridsProofs_NormaliserValuationBound
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_JointServices_VAddEqVw
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open Formalism.BasicNotions (vAdd)
open Formalism.DivisionValues (vw)
noncomputable section
open Formalism Formalism.L2 Formalism.L2.G Formalism.L2.G.ServJoint
variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem Formalism.L2.G.ServJoint.vAdd_eq_vw (w : HeightOneSpectrum (𝓞 K)) (x : K) (hx : x ≠ 0) : vAdd w x = vw w x := by sorry
