-- Prove2me | Theorems.Thm_Formalism_L2_G_ServJoint_VGeq_vw
-- name    : Formalism.L2.G.ServJoint.VGeq.vw
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:50:03.591945+00:00
-- url     : https://prove2.me/theorems/e41871dd-85c7-4974-8056-32bf0d5b6821
-- title:
--   VGeq: vw
-- statement:
--   The VGeq construction uses the vw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/JointServices/VAddEqVw.lean#L107-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/JointServices/VAddEqVw.lean#L107-L114

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

theorem Formalism.L2.G.ServJoint.VGeq.vw {w : HeightOneSpectrum (𝓞 K)} {s : ℝ} {z : K} (h : VGeq w s z) : z = 0 ∨ s ≤ (Formalism.DivisionValues.vw w z : ℝ) := by sorry
