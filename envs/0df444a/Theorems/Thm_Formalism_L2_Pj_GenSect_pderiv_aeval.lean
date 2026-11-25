-- Prove2me | Theorems.Thm_Formalism_L2_Pj_GenSect_pderiv_aeval
-- name    : Formalism.L2.Pj.GenSect.pderiv_aeval
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T01:32:04.146532+00:00
-- url     : https://prove2.me/theorems/300f23e3-889e-4e5d-ad73-afb282e6f6a7
-- title:
--   Gen Sect: pderiv aeval
-- statement:
--   The Gen Sect construction uses the pderiv aeval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/GenSectA.lean#L259-L288
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/GenSectA.lean#L259-L288

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

theorem Formalism.L2.Pj.GenSect.pderiv_aeval {ι : Type*} [Fintype ι] [DecidableEq ι] (j₀ : Fin m) (u : ι → CT Ω D j₀)
    (q : {p : Fin (D + 1) × Fin m // ¬ Zs j₀ p}) (G : MvPolynomial ι K) :
    pderiv q (aeval u G) = ∑ p, aeval u (pderiv p G) * pderiv q (u p) := by sorry
