-- Prove2me | Theorems.Thm_Formalism_L2_Pj_GenSect_pderiv_xv
-- name    : Formalism.L2.Pj.GenSect.pderiv_xv
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T01:31:57.906333+00:00
-- url     : https://prove2.me/theorems/5f7fad85-fbad-4a3b-a0da-3c2036032484
-- title:
--   Gen Sect: pderiv xv
-- statement:
--   The Gen Sect construction uses the pderiv xv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/GenSectA.lean#L222-L233
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/GenSectA.lean#L222-L233

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

theorem Formalism.L2.Pj.GenSect.pderiv_xv (j₀ : Fin m) (q : {p : Fin (D + 1) × Fin m // ¬ Zs j₀ p}) (p : Fin (D + 1) × Fin m) :
    pderiv q (xv (Ω := Ω) j₀ p) = if p = q.1 then 1 else 0 := by sorry
