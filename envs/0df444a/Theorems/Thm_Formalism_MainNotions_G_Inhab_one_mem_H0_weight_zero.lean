-- Prove2me | Theorems.Thm_Formalism_MainNotions_G_Inhab_one_mem_H0_weight_zero
-- name    : Formalism.MainNotions.G.Inhab.one_mem_H0_weight_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:41:24.34382+00:00
-- url     : https://prove2.me/theorems/bbb8098b-0886-4072-9f24-7fa0bc3da85b
-- title:
--   Inhab: one mem H0 weight zero
-- statement:
--   The Inhab construction uses the one mem H0 weight zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/TensorLatticeBounds/DataForm.lean#L51-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/TensorLatticeBounds/DataForm.lean#L51-L56

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TensorLatticeBounds_DataLoc
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TensorLatticeBounds_DataForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.G.Inhab
open Formalism.MainNotions.G Formalism.GradedWeylDivisibility MvPolynomial
variable (R K : Type*) [CommRing R] [Field K] [Algebra R K]

theorem Formalism.MainNotions.G.Inhab.one_mem_H0_weight_zero (m : ℕ) (Λ : Submodule R (Fin (m + 1) → K)) : (1 : MvPolynomial _ K) ∈ H0 R m 0 Λ := by sorry
