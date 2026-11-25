-- Prove2me | Theorems.Thm_Formalism_L2_Pj_GenSect_algKTR_apply
-- name    : Formalism.L2.Pj.GenSect.algKTR_apply
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T01:37:42.636547+00:00
-- url     : https://prove2.me/theorems/49189fd2-7330-50d9-b423-9546be0a657d
-- title:
--   Gen Sect: alg KTR apply
-- statement:
--   The Gen Sect construction uses the alg KTR apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/GenSectC.lean#L17-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/GenSectC.lean#L17-L20

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_GenSectB
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_GenSectC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.GenSect
open MvPolynomial
open scoped TensorProduct
variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {D m : ℕ}

theorem Formalism.L2.Pj.GenSect.algKTR_apply (q : KT K D m) :
    algebraMap (KTf K D m) (RS K Ω D m) (algebraMap (KT K D m) (KTf K D m) q) =
      algebraMap (ΩT Ω D m) (RS K Ω D m) (ktToΩ K Ω D m q) := by sorry
