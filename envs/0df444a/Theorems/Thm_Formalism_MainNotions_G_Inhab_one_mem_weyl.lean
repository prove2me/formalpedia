-- Prove2me | Theorems.Thm_Formalism_MainNotions_G_Inhab_one_mem_weyl
-- name    : Formalism.MainNotions.G.Inhab.one_mem_weyl
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T09:55:21.890801+00:00
-- url     : https://prove2.me/theorems/12cecf93-7421-4b91-b21f-f18028decf0f
-- title:
--   Inhab: one mem weyl
-- statement:
--   The Inhab construction uses the one mem weyl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/TensorLatticeBounds/DataForm.lean#L20-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/TensorLatticeBounds/DataForm.lean#L20-L23

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

theorem Formalism.MainNotions.G.Inhab.one_mem_weyl (k : ℕ) : (1 : MvPolynomial (Fin k × Fin k) R) ∈ weyl R k k le_rfl 0 := by sorry
