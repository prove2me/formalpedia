-- Prove2me | Theorems.Thm_Formalism_L2_Pj_GenSect_psi_incl
-- name    : Formalism.L2.Pj.GenSect.psi_incl
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T11:46:58.776269+00:00
-- url     : https://prove2.me/theorems/33f25ec8-8218-4054-b8eb-682481381d77
-- title:
--   Gen Sect: psi incl
-- statement:
--   The Gen Sect construction uses the psi incl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/GenSectA.lean#L89-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/GenSectA.lean#L89-L96

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

theorem Formalism.L2.Pj.GenSect.psi_incl (x : Fin m → Ω) (j₀ : Fin m) (f : CT Ω D j₀) : psi x j₀ (incl j₀ f) = f := by sorry
