-- Prove2me | Theorems.Thm_Formalism_MainNotions_G_Inhab_one_mem_dualWeyl
-- name    : Formalism.MainNotions.G.Inhab.one_mem_dualWeyl
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:41:52.634652+00:00
-- url     : https://prove2.me/theorems/32d89c67-5f4e-484e-976f-561cd1695346
-- title:
--   Inhab: one mem dual Weyl
-- statement:
--   The Inhab construction uses the one mem dual Weyl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/TensorLatticeBounds/DataForm.lean#L13-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/TensorLatticeBounds/DataForm.lean#L13-L18

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TensorLatticeBounds_DataLoc
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TensorLatticeBounds_DataForm
import Theorems.Thm_Formalism_GradedWeylDivisibility_one_mem_dualWeyl

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

theorem Formalism.MainNotions.G.Inhab.one_mem_dualWeyl (r n : ℕ) : (1 : MvPolynomial (Fin r × Fin n) R) ∈ dualWeyl R r n 0 := by sorry
