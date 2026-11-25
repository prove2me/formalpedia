-- Prove2me | Theorems.Thm_Formalism_L2_GlobalTheoryTheory_FiltrationBoundaryCriterion_CompactFixesLatticeTheory_exists_den_of_isCompact_adele
-- name    : Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.exists_den_of_isCompact_adele
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:44:58.83521+00:00
-- url     : https://prove2.me/theorems/9254e6cb-bed9-5a1a-b48f-6f90e90c110d
-- title:
--   Compact Fixes Lattice Theory: exists den of is Compact adele
-- statement:
--   The Compact Fixes Lattice Theory construction uses the exists den of is Compact adele property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL1/CompactFixesLattice/ExistsDenOfIsCompactAdele.lean#L28-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL1/CompactFixesLattice/ExistsDenOfIsCompactAdele.lean#L28-L52

import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL1_CompactFixesLattice_CompactFixesLattice
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL1_CompactFixesLattice_AdeleIntA
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL1_CompactFixesLattice_ExistsDenOfIsCompactAdele
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

theorem Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.exists_den_of_isCompact_adele (C : Set (AF F)) (hC : IsCompact C) :
    ∃ d : 𝓞 F, d ≠ 0 ∧ ∀ a ∈ C, (d : F) • a ∈ intAd F := by sorry
