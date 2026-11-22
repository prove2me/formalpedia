-- Prove2me | Theorems.Thm_Formalism_HermitianLatticesTheory_locDual_h_smul_left
-- name    : Formalism.HermitianLatticesTheory.locDual_h_smul_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:47:33.596806+00:00
-- url     : https://prove2.me/theorems/b6f180ca-e8d8-4c70-9b67-2c258a68ddd9
-- title:
--   Hermitian Lattices Theory: loc Dual h smul left
-- statement:
--   The Hermitian Lattices Theory construction uses the loc Dual h smul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/LocDual.lean#L29-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/LocDual.lean#L29-L32

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

theorem Formalism.HermitianLatticesTheory.locDual_h_smul_left (h : V →ₗ⋆[K] V →ₗ[K] K) (r : R) (y x : V) :
    h (r • y) x = star (algebraMap R K r) * h y x := by sorry
