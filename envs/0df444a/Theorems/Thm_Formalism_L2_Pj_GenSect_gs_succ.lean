-- Prove2me | Theorems.Thm_Formalism_L2_Pj_GenSect_gs_succ
-- name    : Formalism.L2.Pj.GenSect.gs_succ
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T01:32:46.897865+00:00
-- url     : https://prove2.me/theorems/99e9c813-915f-41da-a6e2-38ba8869e6d1
-- title:
--   Gen Sect: gs succ
-- statement:
--   The Gen Sect construction uses the gs succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/GenSectA.lean#L98-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/GenSectA.lean#L98-L110

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

theorem Formalism.L2.Pj.GenSect.gs_succ (x : Fin m → Ω) (j₀ : Fin m) (i : Fin D) (j : Fin m) :
    gs x j₀ (i.succ, j) = xv j₀ (i.succ, j) +
      if j = j₀ then -∑ k, xv j₀ (i.succ, k) * C (rr x j₀ k) else 0 := by sorry
