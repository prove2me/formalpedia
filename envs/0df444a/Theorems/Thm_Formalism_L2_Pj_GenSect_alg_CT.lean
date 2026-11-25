-- Prove2me | Theorems.Thm_Formalism_L2_Pj_GenSect_alg_CT
-- name    : Formalism.L2.Pj.GenSect.alg_CT
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T01:32:51.478015+00:00
-- url     : https://prove2.me/theorems/7286f41f-9794-4268-ab68-6873e9694e11
-- title:
--   Gen Sect: alg CT
-- statement:
--   The Gen Sect construction uses the alg CT property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/GenSectB.lean#L116-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/GenSectB.lean#L116-L145

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

theorem Formalism.L2.Pj.GenSect.alg_CT (x : Fin m → Ω) (j₀ : Fin m)
    (halg : ∀ ω : Ω, IsAlgebraic (Algebra.adjoin K (Set.range (rr x j₀))) ω)
    (hr : ∀ k, IsAlgebraic (Algebra.adjoin K (Set.range (gs (D := D) x j₀)))
      (C (rr x j₀ k) : CT Ω D j₀)) :
    Algebra.IsAlgebraic (Algebra.adjoin K (Set.range (gs (D := D) x j₀))) (CT Ω D j₀) := by sorry
