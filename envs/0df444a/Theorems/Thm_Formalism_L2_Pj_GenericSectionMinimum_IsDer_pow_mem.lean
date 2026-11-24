-- Prove2me | Theorems.Thm_Formalism_L2_Pj_GenericSectionMinimum_IsDer_pow_mem
-- name    : Formalism.L2.Pj.GenericSectionMinimum.IsDer.pow_mem
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:38:11.563797+00:00
-- url     : https://prove2.me/theorems/f83e68c6-e223-4ce3-8cb5-53161754030f
-- title:
--   Is Der: pow mem
-- statement:
--   The Is Der construction uses the pow mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/PowMapMemOfPowMulMem.lean#L77-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/PowMapMemOfPowMulMem.lean#L77-L80

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

theorem Formalism.L2.Pj.GenericSectionMinimum.IsDer.pow_mem (h : IsDer δ) (I : Ideal A) (hI : ∀ x ∈ I, δ x ∈ I) (hu : ∀ n : ℕ, 0 < n → IsUnit (n : A))
    {y : A} {n : ℕ} (hy : y ^ n ∈ I) : δ y ^ (2 * n) ∈ I := by sorry
