-- Prove2me | Theorems.Thm_Formalism_L2_Pj_LocalUnitReduction_mem_sup_ker
-- name    : Formalism.L2.Pj.LocalUnitReduction.mem_sup_ker
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T03:58:11.906816+00:00
-- url     : https://prove2.me/theorems/0b3f42be-f97f-4981-9395-e20194e6a442
-- title:
--   Local Unit Reduction: mem sup ker
-- statement:
--   The Local Unit Reduction construction uses the mem sup ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/LocalUnitReduction/IsUnitMkOfForallPrime.lean#L23-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/LocalUnitReduction/IsUnitMkOfForallPrime.lean#L23-L75

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

theorem Formalism.L2.Pj.LocalUnitReduction.mem_sup_ker {c : ι}
    (hloc : ∀ r : R c, ∃ a p : Fr,
      (∀ Q : Ideal Fr, Q.IsPrime → J ≤ Q → RingHom.ker (φ c) ≤ Q → p ∉ Q) ∧ φ c p * r = φ c a)
    {f : Fr} (hf : φ c f ∈ Ideal.map (φ c) J) : f ∈ J ⊔ RingHom.ker (φ c) := by sorry
