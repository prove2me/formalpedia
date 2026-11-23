-- Prove2me | Theorems.Thm_Formalism_L2_G_ServJoint_VGeq_add
-- name    : Formalism.L2.G.ServJoint.VGeq.add
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:49:39.023087+00:00
-- url     : https://prove2.me/theorems/c5213e1a-6157-49f9-8dc4-70a4507658ce
-- title:
--   VGeq: add
-- statement:
--   The VGeq construction uses the add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/JointServices/VAddEqVw.lean#L71-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/JointServices/VAddEqVw.lean#L71-L86

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

theorem Formalism.L2.G.ServJoint.VGeq.add {w : HeightOneSpectrum (𝓞 K)} {s : ℝ} {a b : K} (ha : VGeq w s a) (hb : VGeq w s b) :
    VGeq w s (a + b) := by sorry
