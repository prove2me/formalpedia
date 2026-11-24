-- Prove2me | Theorems.Thm_Formalism_HermitianLatticesTheory_indexBasic_dual_le_fg
-- name    : Formalism.HermitianLatticesTheory.indexBasic_dual_le_fg
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:04:24.685625+00:00
-- url     : https://prove2.me/theorems/f9e86528-b95d-4732-8d43-d445c38a2d71
-- title:
--   Hermitian Lattices Theory: index Basic dual le fg
-- statement:
--   The Hermitian Lattices Theory construction uses the index Basic dual le fg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/IndexBasic.lean#L221-L267
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/IndexBasic.lean#L221-L267

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
noncomputable section
open Formalism Formalism.HermitianLatticesTheory

theorem Formalism.HermitianLatticesTheory.indexBasic_dual_le_fg {R K V : Type*} [CommRing R] [Field K] [StarRing K] [Algebra R K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module R V] [IsScalarTower R K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K) (hnd : h.Nondegenerate) (A : Submodule R V)
    (hA : Submodule.span K (A : Set V) = ⊤) :
    ∃ F : Submodule R V, F.FG ∧ dual h A ≤ F := by sorry
