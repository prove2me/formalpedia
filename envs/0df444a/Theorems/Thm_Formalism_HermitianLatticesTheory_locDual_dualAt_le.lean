-- Prove2me | Theorems.Thm_Formalism_HermitianLatticesTheory_locDual_dualAt_le
-- name    : Formalism.HermitianLatticesTheory.locDual_dualAt_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:26:58.268421+00:00
-- url     : https://prove2.me/theorems/207519c3-6809-4c3f-9bc9-6092a12ad658
-- title:
--   Hermitian Lattices Theory: loc Dual dual At le
-- statement:
--   The Hermitian Lattices Theory construction uses the loc Dual dual At le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/LocDual.lean#L64-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/LocDual.lean#L64-L92

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

theorem Formalism.HermitianLatticesTheory.locDual_dualAt_le (h : V →ₗ⋆[K] V →ₗ[K] K)
    (hstar : ∀ r : R, star (algebraMap R K r) ∈ Set.range (algebraMap R K))
    (p : Ideal R) (L : Submodule R V) (hL : L.FG) :
    dualAt h p L ≤ loc (K := K) p (dual h L) := by sorry
