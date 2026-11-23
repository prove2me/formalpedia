-- Prove2me | Theorems.Thm_Formalism_MainNotions_G_Inhab_lamAt_zero
-- name    : Formalism.MainNotions.G.Inhab.lamAt_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:56:09.459476+00:00
-- url     : https://prove2.me/theorems/63c6b57d-1bbb-4492-ad95-91ad67621f3f
-- title:
--   Inhab: lam At zero
-- statement:
--   The Inhab construction uses the lam At zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/TensorLatticeBounds/DataForm.lean#L65-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/TensorLatticeBounds/DataForm.lean#L65-L68

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

theorem Formalism.MainNotions.G.Inhab.lamAt_zero {n' m : ℕ} (s : Fin n') : lamAt (fun _ _ => 0 : Fin n' → Fin (m + 1) → ℤ) s = 0 := by sorry
