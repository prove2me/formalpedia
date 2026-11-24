-- Prove2me | Theorems.Thm_Formalism_MainNotions_G_Inhab_one_mem_lattice_degree_zero
-- name    : Formalism.MainNotions.G.Inhab.one_mem_lattice_degree_zero
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T09:55:44.661371+00:00
-- url     : https://prove2.me/theorems/d685fe44-f36f-422a-9a58-6975d22b04a1
-- title:
--   Inhab: one mem lattice degree zero
-- statement:
--   The Inhab construction uses the one mem lattice degree zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/TensorLatticeBounds/DataForm.lean#L58-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/TensorLatticeBounds/DataForm.lean#L58-L63

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

theorem Formalism.MainNotions.G.Inhab.one_mem_lattice_degree_zero (m : ℕ) (Λ : Submodule R (Fin (m + 1) → K)) : (1 : MvPolynomial _ K) ∈ Dl0 R m 0 Λ := by sorry
