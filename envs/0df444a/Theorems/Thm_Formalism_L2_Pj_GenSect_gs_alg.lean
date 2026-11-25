-- Prove2me | Theorems.Thm_Formalism_L2_Pj_GenSect_gs_alg
-- name    : Formalism.L2.Pj.GenSect.gs_alg
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T01:32:29.750901+00:00
-- url     : https://prove2.me/theorems/09e3f421-84df-4d4f-9b91-8f092e411f04
-- title:
--   Gen Sect: gs alg
-- statement:
--   The Gen Sect construction uses the gs alg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/GenSectB.lean#L241-L246
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/GenSectB.lean#L241-L246

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_GenSectA
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_GenSectB
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
open MvPolynomial Cardinal
variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {D m : ℕ}

theorem Formalism.L2.Pj.GenSect.gs_alg [CharZero K] (x : Fin m → Ω) (j₀ : Fin m) (hx₀ : x j₀ ≠ 0)
    (htr : Algebra.trdeg K Ω = D)
    (halg : ∀ ω : Ω, IsAlgebraic (Algebra.adjoin K (Set.range (rr x j₀))) ω) :
    Algebra.IsAlgebraic (Algebra.adjoin K (Set.range (gs (D := D) x j₀))) (CT Ω D j₀) := by sorry
