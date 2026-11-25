-- Prove2me | Theorems.Thm_Formalism_L2_Pj_GenSect_psi_X
-- name    : Formalism.L2.Pj.GenSect.psi_X
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T01:22:06.187786+00:00
-- url     : https://prove2.me/theorems/00619c27-fb94-4e95-beb4-bd640565b4f6
-- title:
--   Gen Sect: psi X
-- statement:
--   The Gen Sect construction uses the psi X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/GenSectA.lean#L70-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/GenSectA.lean#L70-L74

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

theorem Formalism.L2.Pj.GenSect.psi_X (x : Fin m → Ω) (j₀ : Fin m) (p : Fin (D + 1) × Fin m) :
    psi x j₀ (X p) = gs x j₀ p := by sorry
