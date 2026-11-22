-- Prove2me | Theorems.Thm_Formalism_HermitianLatticesTheory_genusBasic_mem_one_mul
-- name    : Formalism.HermitianLatticesTheory.genusBasic_mem_one_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:08:41.091593+00:00
-- url     : https://prove2.me/theorems/ed9eaa4e-e3cf-47cb-94e2-e515ed49b051
-- title:
--   Hermitian Lattices Theory: genus Basic mem one mul
-- statement:
--   The Hermitian Lattices Theory construction uses the genus Basic mem one mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/GenusBasic.lean#L36-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/GenusBasic.lean#L36-L39

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IsomAct
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusBasic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
variable {R K V : Type*} [CommRing R] [Field K] [StarRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

theorem Formalism.HermitianLatticesTheory.genusBasic_mem_one_mul (x : K) (hx : x ∈ (1 : Submodule R K)) (r : R) :
    algebraMap R K r * x ∈ (1 : Submodule R K) := by sorry
