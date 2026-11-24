-- Prove2me | Theorems.Thm_Formalism_L2_GlobalTheoryTheory_FiltrationBoundaryCriterion_CompactFixesLatticeTheory_exists_den_of_isCompact
-- name    : Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.exists_den_of_isCompact
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:57:37.75737+00:00
-- url     : https://prove2.me/theorems/2f64c60c-4cde-45cf-be05-5714e863e920
-- title:
--   Compact Fixes Lattice Theory: exists den of is Compact
-- statement:
--   The Compact Fixes Lattice Theory construction uses the exists den of is Compact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL1/CompactFixesLattice/ExistsDenOfIsCompact.lean#L80-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL1/CompactFixesLattice/ExistsDenOfIsCompact.lean#L80-L143

import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL1_CompactFixesLattice_MemClosureOfMemSS
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL1_CompactFixesLattice_Imports
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL1_CompactFixesLattice_ExistsDenOfIsCompact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.exists_den_of_isCompact :
    letI := tensTop (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
    ∀ C : Set (AE F E), IsCompact C → ∃ d : 𝓞 F, d ≠ 0 ∧ ∀ x ∈ C, (d : F) • x ∈ SS F E := by sorry
