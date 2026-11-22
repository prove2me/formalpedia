-- Prove2me | Theorems.Thm_Formalism_HermitianLatticesTheory_locDual_mem_locR
-- name    : Formalism.HermitianLatticesTheory.locDual_mem_locR
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:02:23.021451+00:00
-- url     : https://prove2.me/theorems/ae09fef7-c2a9-41b7-8494-04df967d4f9d
-- title:
--   Hermitian Lattices Theory: loc Dual mem loc R
-- statement:
--   The Hermitian Lattices Theory construction uses the loc Dual mem loc R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/LocDual.lean#L19-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/LocDual.lean#L19-L23

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocDual
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

theorem Formalism.HermitianLatticesTheory.locDual_mem_locR (p : Ideal R) (k : K) :
    k ∈ locR (K := K) p ↔
      ∃ s ∈ hcompl (K := K) p, algebraMap R K s * k ∈ (1 : Submodule R K) := by sorry
