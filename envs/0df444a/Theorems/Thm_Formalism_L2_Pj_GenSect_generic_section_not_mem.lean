-- Prove2me | Theorems.Thm_Formalism_L2_Pj_GenSect_generic_section_not_mem
-- name    : Formalism.L2.Pj.GenSect.generic_section_not_mem
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:46:50.193794+00:00
-- url     : https://prove2.me/theorems/49f8e809-1f25-5e89-afe2-c77ba23afb0c
-- title:
--   Gen Sect: generic section not mem
-- statement:
--   The Gen Sect construction uses the generic section not mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/GenSectT.lean#L31-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/GenSectT.lean#L31-L62

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_GenSect
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_GenSectT
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
variable (K Ω Kl K' : Type) [Field K] [Field Ω] [Algebra K Ω] [Field Kl] [Field K'] [Algebra K Kl]
  [Algebra Kl K'] [Algebra K K'] [IsScalarTower K Kl K']
variable {K Ω Kl K'} {D m : ℕ}
omit [Field Kl] [Field K'] [Algebra K Kl] [Algebra Kl K'] [Algebra K K'] [IsScalarTower K Kl K']

theorem Formalism.L2.Pj.GenSect.generic_section_not_mem [CharZero K] (htr : Algebra.trdeg K Ω = D) (x : Fin m → Ω) (k₀ : Fin m) (hx₁ : x k₀ = 1)
    (halg : ∀ ω : Ω, IsAlgebraic (Algebra.adjoin K (Set.range (rr x k₀))) ω) :
    algebraMap (ΩT Ω D m) (RS K Ω D m) (∑ k, X ((0 : Fin (D + 1)), k) * C (x k)) ∉ Is K x := by sorry
