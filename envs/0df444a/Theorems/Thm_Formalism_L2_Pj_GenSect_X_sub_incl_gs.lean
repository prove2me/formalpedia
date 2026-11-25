-- Prove2me | Theorems.Thm_Formalism_L2_Pj_GenSect_X_sub_incl_gs
-- name    : Formalism.L2.Pj.GenSect.X_sub_incl_gs
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T01:32:35.467428+00:00
-- url     : https://prove2.me/theorems/5615c8ab-fb42-4e55-8187-b9375761055e
-- title:
--   Gen Sect: X sub incl gs
-- statement:
--   The Gen Sect construction uses the X sub incl gs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/GenSectA.lean#L154-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/GenSectA.lean#L154-L169

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

theorem Formalism.L2.Pj.GenSect.X_sub_incl_gs (x : Fin m → Ω) (j₀ : Fin m) (hx₀ : x j₀ ≠ 0) (i : Fin D) :
    X (i.succ, j₀) - incl j₀ (gs x j₀ (i.succ, j₀)) = C (x j₀)⁻¹ * sec x i := by sorry
