-- Prove2me | Theorems.Thm_Formalism_L2_Pj_GenericSectionMinimum_IsDer_mul_map_pow
-- name    : Formalism.L2.Pj.GenericSectionMinimum.IsDer.mul_map_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:44:35.753984+00:00
-- url     : https://prove2.me/theorems/5cfc6857-0de3-4236-a166-252f544403e9
-- title:
--   Is Der: mul map pow
-- statement:
--   The Is Der construction uses the mul map pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/PowMapMemOfPowMulMem.lean#L43-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/PowMapMemOfPowMulMem.lean#L43-L49

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

theorem Formalism.L2.Pj.GenericSectionMinimum.IsDer.mul_map_pow (h : IsDer δ) (z : A) (r : ℕ) : z * δ (z ^ r) = (r : A) * z ^ r * δ z := by sorry
