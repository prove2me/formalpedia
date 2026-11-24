-- Prove2me | Theorems.Thm_Formalism_L2_GlobalTheoryTheory_FiltrationBoundaryCriterion_CompactFixesLatticeTheory_mul_mem_closure_tmul
-- name    : Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.mul_mem_closure_tmul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:57:46.42082+00:00
-- url     : https://prove2.me/theorems/21d95851-f7b4-4f95-82c4-812412134795
-- title:
--   Compact Fixes Lattice Theory: mul mem closure tmul
-- statement:
--   The Compact Fixes Lattice Theory construction uses the mul mem closure tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL1/CompactFixesLattice/MemClosureOfMemSS.lean#L30-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL1/CompactFixesLattice/MemClosureOfMemSS.lean#L30-L47

import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL1_CompactFixesLattice_CoordMulTmul
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL1_CompactFixesLattice_ExistsDenOfIsCompactAdele
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL1_CompactFixesLattice_MemClosureOfMemSS
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

theorem Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.mul_mem_closure_tmul {y z : AE F E}
    (hy : y ∈ AddSubgroup.closure {y : AE F E | ∃ e ∈ intOE E, ∃ a ∈ intAd F, y = e ⊗ₜ[F] a})
    (hz : z ∈ AddSubgroup.closure {y : AE F E | ∃ e ∈ intOE E, ∃ a ∈ intAd F, y = e ⊗ₜ[F] a}) :
    y * z ∈ AddSubgroup.closure {y : AE F E | ∃ e ∈ intOE E, ∃ a ∈ intAd F, y = e ⊗ₜ[F] a} := by sorry
