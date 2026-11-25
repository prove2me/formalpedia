-- Prove2me | Theorems.Thm_Formalism_L2_Pj_GenSect_pderiv_gs
-- name    : Formalism.L2.Pj.GenSect.pderiv_gs
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T01:31:55.785428+00:00
-- url     : https://prove2.me/theorems/b24173c2-aaf0-48f8-ab3a-21d3a38f5c7b
-- title:
--   Gen Sect: pderiv gs
-- statement:
--   The Gen Sect construction uses the pderiv gs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/GenSectA.lean#L235-L257
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/GenSectA.lean#L235-L257

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

theorem Formalism.L2.Pj.GenSect.pderiv_gs (x : Fin m → Ω) (j₀ : Fin m) (q : {p : Fin (D + 1) × Fin m // ¬ Zs j₀ p})
    (p : Fin (D + 1) × Fin m) :
    pderiv q (gs x j₀ p) = (if p = q.1 then 1 else 0) -
      if Zs j₀ p ∧ p.1 = q.1.1 then C (rr x j₀ q.1.2) else 0 := by sorry
