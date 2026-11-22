-- Prove2me | Theorems.Thm_Formalism_HermitianLatticesTheory_dualLattice_dualBasis
-- name    : Formalism.HermitianLatticesTheory.dualLattice_dualBasis
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:31:29.230963+00:00
-- url     : https://prove2.me/theorems/390ed2e3-6767-46b3-a35c-84d5cfb3c3a8
-- title:
--   Hermitian Lattices Theory: dual Lattice dual Basis
-- statement:
--   The Hermitian Lattices Theory construction uses the dual Lattice dual Basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/DualLattice.lean#L76-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/DualLattice.lean#L76-L93

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualLattice
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
variable {R K V : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
variable [StarRing K]

theorem Formalism.HermitianLatticesTheory.dualLattice_dualBasis {ι : Type*} [Fintype ι] [DecidableEq ι] (h : V →ₗ⋆[K] V →ₗ[K] K)
    (hnd : h.Nondegenerate) (b : Basis ι K V) :
    ∃ bs : ι → V, ∀ i j, h (b i) (bs j) = if i = j then 1 else 0 := by sorry
