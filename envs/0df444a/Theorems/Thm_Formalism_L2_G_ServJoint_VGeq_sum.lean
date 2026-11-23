-- Prove2me | Theorems.Thm_Formalism_L2_G_ServJoint_VGeq_sum
-- name    : Formalism.L2.G.ServJoint.VGeq.sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:51:38.858707+00:00
-- url     : https://prove2.me/theorems/a1089799-985c-490c-ab5d-f2357383413f
-- title:
--   VGeq: sum
-- statement:
--   The VGeq construction uses the sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/JointServices/VAddEqVw.lean#L103-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/JointServices/VAddEqVw.lean#L103-L105

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

theorem Formalism.L2.G.ServJoint.VGeq.sum {w : HeightOneSpectrum (𝓞 K)} {s : ℝ} {ι : Type*} (S : Finset ι) (f : ι → K)
    (h : ∀ i ∈ S, VGeq w s (f i)) : VGeq w s (∑ i ∈ S, f i) := by sorry
