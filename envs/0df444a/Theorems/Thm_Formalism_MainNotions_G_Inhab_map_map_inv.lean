-- Prove2me | Theorems.Thm_Formalism_MainNotions_G_Inhab_map_map_inv
-- name    : Formalism.MainNotions.G.Inhab.map_map_inv
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T09:55:51.914837+00:00
-- url     : https://prove2.me/theorems/98f05131-9261-4fe3-9406-9a9ae0e2793b
-- title:
--   Inhab: map map inv
-- statement:
--   The Inhab construction uses the map map inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/TensorLatticeBounds/DataForm.lean#L92-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/TensorLatticeBounds/DataForm.lean#L92-L100

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
variable {R K : Type*} [CommRing R] [Field K] [Algebra R K] {k : ℕ}

theorem Formalism.MainNotions.G.Inhab.map_map_inv (A : GL (Fin k) K) (L : Submodule R (Fin k → K)) :
    (L.map ((Matrix.mulVecLin (A : Matrix (Fin k) (Fin k) K)).restrictScalars R)).map
      ((Matrix.mulVecLin ((A⁻¹ : GL (Fin k) K) : Matrix (Fin k) (Fin k) K)).restrictScalars R) = L := by sorry
