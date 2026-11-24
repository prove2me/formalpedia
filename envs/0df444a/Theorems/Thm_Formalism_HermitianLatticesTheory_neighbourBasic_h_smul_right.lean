-- Prove2me | Theorems.Thm_Formalism_HermitianLatticesTheory_neighbourBasic_h_smul_right
-- name    : Formalism.HermitianLatticesTheory.neighbourBasic_h_smul_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:05:01.547044+00:00
-- url     : https://prove2.me/theorems/769f885e-0959-484a-9a80-f985dcd9c591
-- title:
--   Hermitian Lattices Theory: neighbour Basic h smul right
-- statement:
--   The Hermitian Lattices Theory construction uses the neighbour Basic h smul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/NeighbourBasic.lean#L155-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/NeighbourBasic.lean#L155-L157

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_NeighbourBasic
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

theorem Formalism.HermitianLatticesTheory.neighbourBasic_h_smul_right (h : V →ₗ⋆[K] V →ₗ[K] K) (a : R) (x y : V) :
    h x (a • y) = algebraMap R K a * h x y := by sorry
