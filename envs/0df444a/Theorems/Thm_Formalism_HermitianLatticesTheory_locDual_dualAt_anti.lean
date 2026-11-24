-- Prove2me | Theorems.Thm_Formalism_HermitianLatticesTheory_locDual_dualAt_anti
-- name    : Formalism.HermitianLatticesTheory.locDual_dualAt_anti
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:04:50.303516+00:00
-- url     : https://prove2.me/theorems/27217372-d945-4d97-acde-5f39c3853022
-- title:
--   Hermitian Lattices Theory: loc Dual dual At anti
-- statement:
--   The Hermitian Lattices Theory construction uses the loc Dual dual At anti property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/LocDual.lean#L41-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/LocDual.lean#L41-L45

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

theorem Formalism.HermitianLatticesTheory.locDual_dualAt_anti (h : V →ₗ⋆[K] V →ₗ[K] K) (p : Ideal R) {L M : Submodule R V}
    (hLM : L ≤ M) : dualAt h p M ≤ dualAt h p L := by sorry
