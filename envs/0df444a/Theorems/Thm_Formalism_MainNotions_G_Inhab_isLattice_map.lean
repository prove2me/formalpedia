-- Prove2me | Theorems.Thm_Formalism_MainNotions_G_Inhab_isLattice_map
-- name    : Formalism.MainNotions.G.Inhab.isLattice_map
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T09:56:08.06979+00:00
-- url     : https://prove2.me/theorems/e56a657d-1fbe-48fa-a759-bda16f1df3be
-- title:
--   Inhab: is Lattice map
-- statement:
--   The Inhab construction uses the is Lattice map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/TensorLatticeBounds/DataForm.lean#L85-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/TensorLatticeBounds/DataForm.lean#L85-L90

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

theorem Formalism.MainNotions.G.Inhab.isLattice_map (A : GL (Fin k) K) {L : Submodule R (Fin k → K)} (hL : IsLattice R L) :
    IsLattice R (L.map ((Matrix.mulVecLin (A : Matrix (Fin k) (Fin k) K)).restrictScalars R)) := by sorry
