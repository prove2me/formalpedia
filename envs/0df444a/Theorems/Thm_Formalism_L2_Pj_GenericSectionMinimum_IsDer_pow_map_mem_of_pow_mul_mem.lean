-- Prove2me | Theorems.Thm_Formalism_L2_Pj_GenericSectionMinimum_IsDer_pow_map_mem_of_pow_mul_mem
-- name    : Formalism.L2.Pj.GenericSectionMinimum.IsDer.pow_map_mem_of_pow_mul_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:38:05.566493+00:00
-- url     : https://prove2.me/theorems/841fe884-7070-42b7-9b9d-b9f0584e083b
-- title:
--   Is Der: pow map mem of pow mul mem
-- statement:
--   The Is Der construction uses the pow map mem of pow mul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/PowMapMemOfPowMulMem.lean#L54-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/PowMapMemOfPowMulMem.lean#L54-L75

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PowMapMemOfPowMulMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.GenericSectionMinimum
open Formalism.L2.Pj.GenericSectionMinimum.IsDer
variable {A : Type*} [CommRing A] {δ : A → A}

theorem Formalism.L2.Pj.GenericSectionMinimum.IsDer.pow_map_mem_of_pow_mul_mem (h : IsDer δ) (I : Ideal A) (hI : ∀ x ∈ I, δ x ∈ I) (hu : ∀ n : ℕ, 0 < n → IsUnit (n : A))
    (y : A) : ∀ m r : ℕ, y ^ m * δ y ^ r ∈ I → δ y ^ (r + 2 * m) ∈ I := by sorry
