-- Prove2me | Theorems.Thm_Formalism_L2_G_ServJoint_VGeq_mono
-- name    : Formalism.L2.G.ServJoint.VGeq.mono
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:50:11.134605+00:00
-- url     : https://prove2.me/theorems/23cc7de8-363c-4a37-a375-115a825c5e1c
-- title:
--   VGeq: mono
-- statement:
--   The VGeq construction uses the mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/JointServices/VAddEqVw.lean#L58-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/JointServices/VAddEqVw.lean#L58-L59

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

theorem Formalism.L2.G.ServJoint.VGeq.mono {w : HeightOneSpectrum (𝓞 K)} {s s' : ℝ} {z : K} (h : VGeq w s z) (hs : s' ≤ s) : VGeq w s' z := by sorry
