-- Prove2me | Theorems.Thm_Formalism_HermitianLatticesTheory_locDual_dualAt_loc
-- name    : Formalism.HermitianLatticesTheory.locDual_dualAt_loc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:27:06.906541+00:00
-- url     : https://prove2.me/theorems/2a625085-da0c-418b-a447-027d5fa01923
-- title:
--   Hermitian Lattices Theory: loc Dual dual At loc
-- statement:
--   The Hermitian Lattices Theory construction uses the loc Dual dual At loc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/LocDual.lean#L112-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/LocDual.lean#L112-L134

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

theorem Formalism.HermitianLatticesTheory.locDual_dualAt_loc (h : V →ₗ⋆[K] V →ₗ[K] K) (hinj : Function.Injective (algebraMap R K))
    (hstar : ∀ r : R, star (algebraMap R K r) ∈ Set.range (algebraMap R K))
    (p : Ideal R) (L : Submodule R V) :
    dualAt h p (loc (K := K) p L) = dualAt h p L := by sorry
