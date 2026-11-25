-- Prove2me | Theorems.Thm_Formalism_L2_Pj_LocalUnitReduction_isUnit_mk_of_forall_prime
-- name    : Formalism.L2.Pj.LocalUnitReduction.isUnit_mk_of_forall_prime
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:46:06.67443+00:00
-- url     : https://prove2.me/theorems/d07dd68c-729d-4efe-a3b3-732340ae2dea
-- title:
--   Local Unit Reduction: is Unit mk of forall prime
-- statement:
--   The Local Unit Reduction construction uses the is Unit mk of forall prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/LocalUnitReduction/IsUnitMkOfForallPrime.lean#L11-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/LocalUnitReduction/IsUnitMkOfForallPrime.lean#L11-L21

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_LocalUnitReduction_FinRedStatement
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_LocalUnitReduction_IsUnitMkOfForallPrime
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.LocalUnitReduction
variable {K' Fr : Type*} [Field K'] [CommRing Fr] [Algebra K' Fr] (J : Ideal Fr)
  {ι : Type*} {R : ι → Type*} [∀ c, CommRing (R c)] [∀ c, Algebra K' (R c)]
  (φ : ∀ c, Fr →ₐ[K'] R c)

theorem Formalism.L2.Pj.LocalUnitReduction.isUnit_mk_of_forall_prime {I : Ideal Fr} {p : Fr}
    (hp : ∀ Q : Ideal Fr, Q.IsPrime → I ≤ Q → p ∉ Q) : IsUnit (Ideal.Quotient.mk I p) := by sorry
