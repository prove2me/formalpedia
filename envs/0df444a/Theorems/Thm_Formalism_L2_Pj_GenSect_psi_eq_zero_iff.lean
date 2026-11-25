-- Prove2me | Theorems.Thm_Formalism_L2_Pj_GenSect_psi_eq_zero_iff
-- name    : Formalism.L2.Pj.GenSect.psi_eq_zero_iff
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T01:32:08.425864+00:00
-- url     : https://prove2.me/theorems/9b0e2e6f-178d-4601-a2d3-e6e0c92d8c84
-- title:
--   Gen Sect: psi eq zero iff
-- statement:
--   The Gen Sect construction uses the psi eq zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/GenSectA.lean#L209-L220
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/GenSectA.lean#L209-L220

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

theorem Formalism.L2.Pj.GenSect.psi_eq_zero_iff (x : Fin m → Ω) (j₀ : Fin m) (hx₀ : x j₀ ≠ 0) (f : ΩT Ω D m) :
    psi x j₀ f = 0 ↔ f ∈ Ideal.span (Set.range (sec x)) := by sorry
