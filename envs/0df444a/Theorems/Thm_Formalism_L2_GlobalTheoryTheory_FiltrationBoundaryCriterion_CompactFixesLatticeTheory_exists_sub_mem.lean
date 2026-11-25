-- Prove2me | Theorems.Thm_Formalism_L2_GlobalTheoryTheory_FiltrationBoundaryCriterion_CompactFixesLatticeTheory_exists_sub_mem
-- name    : Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.exists_sub_mem
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:44:49.511463+00:00
-- url     : https://prove2.me/theorems/37d94982-2567-4da8-bc30-554862cb30aa
-- title:
--   Compact Fixes Lattice Theory: exists sub mem
-- statement:
--   The Compact Fixes Lattice Theory construction uses the exists sub mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL1/CompactFixesLattice/ExistsDenOfIsCompact.lean#L22-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL1/CompactFixesLattice/ExistsDenOfIsCompact.lean#L22-L28

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

theorem Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.exists_sub_mem (x : AE F E) : ∃ e : E, x - inclE (F := F) (AF F) e ∈ SS F E := by sorry
