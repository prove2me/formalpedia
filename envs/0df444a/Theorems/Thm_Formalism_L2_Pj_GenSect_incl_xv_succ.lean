-- Prove2me | Theorems.Thm_Formalism_L2_Pj_GenSect_incl_xv_succ
-- name    : Formalism.L2.Pj.GenSect.incl_xv_succ
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T01:32:50.799475+00:00
-- url     : https://prove2.me/theorems/2670b82d-d0b3-4cde-8853-22fe5ec3dde9
-- title:
--   Gen Sect: incl xv succ
-- statement:
--   The Gen Sect construction uses the incl xv succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/GenSectA.lean#L141-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/GenSectA.lean#L141-L152

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_GenSectA
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
variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (D m : ℕ)
variable {K Ω D m}

theorem Formalism.L2.Pj.GenSect.incl_xv_succ (j₀ : Fin m) (i : Fin D) (k : Fin m) :
    incl (Ω := Ω) j₀ (xv j₀ (i.succ, k)) = if k = j₀ then 0 else X (i.succ, k) := by sorry
