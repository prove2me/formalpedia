-- Prove2me | Theorems.Thm_Formalism_L2_Pj_GenSect_sub_incl_psi_mem
-- name    : Formalism.L2.Pj.GenSect.sub_incl_psi_mem
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T01:32:08.39912+00:00
-- url     : https://prove2.me/theorems/f6e6f956-d304-4f0c-99b1-65e80d151b49
-- title:
--   Gen Sect: sub incl psi mem
-- statement:
--   The Gen Sect construction uses the sub incl psi mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/GenSectA.lean#L171-L207
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/GenSectA.lean#L171-L207

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

theorem Formalism.L2.Pj.GenSect.sub_incl_psi_mem (x : Fin m → Ω) (j₀ : Fin m) (hx₀ : x j₀ ≠ 0) (f : ΩT Ω D m) :
    f - incl j₀ (psi x j₀ f) ∈ Ideal.span (Set.range (sec x)) := by sorry
