-- Prove2me | Theorems.Thm_Formalism_HermitianLatticesTheory_locDual_mem_dualAt
-- name    : Formalism.HermitianLatticesTheory.locDual_mem_dualAt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:01:37.941547+00:00
-- url     : https://prove2.me/theorems/d9de76e7-dd5c-4081-8276-2309775cea1b
-- title:
--   Hermitian Lattices Theory: loc Dual mem dual At
-- statement:
--   The Hermitian Lattices Theory construction uses the loc Dual mem dual At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/LocDual.lean#L15-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/LocDual.lean#L15-L17

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

theorem Formalism.HermitianLatticesTheory.locDual_mem_dualAt (h : V →ₗ⋆[K] V →ₗ[K] K) (p : Ideal R) (L : Submodule R V) (x : V) :
    x ∈ dualAt h p L ↔ ∀ y ∈ L, h y x ∈ locR (K := K) p := by sorry
