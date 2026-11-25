-- Prove2me | Theorems.Thm_Formalism_L2_Pj_GenSect_xv_of_not
-- name    : Formalism.L2.Pj.GenSect.xv_of_not
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T01:22:20.517896+00:00
-- url     : https://prove2.me/theorems/925a82a3-d898-4e02-b434-5a59f6204cfb
-- title:
--   Gen Sect: xv of not
-- statement:
--   The Gen Sect construction uses the xv of not property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/GenSectA.lean#L58-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/GenSectA.lean#L58-L62

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

theorem Formalism.L2.Pj.GenSect.xv_of_not {j₀ : Fin m} {p : Fin (D + 1) × Fin m} (h : ¬ Zs j₀ p) :
    xv (Ω := Ω) j₀ p = X ⟨p, h⟩ := by sorry
