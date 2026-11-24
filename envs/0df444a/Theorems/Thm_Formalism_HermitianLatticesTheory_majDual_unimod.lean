-- Prove2me | Theorems.Thm_Formalism_HermitianLatticesTheory_majDual_unimod
-- name    : Formalism.HermitianLatticesTheory.majDual_unimod
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:04:58.138796+00:00
-- url     : https://prove2.me/theorems/84aa1f87-5feb-4f18-993a-dc90a9c2b9cd
-- title:
--   Hermitian Lattices Theory: maj Dual unimod
-- statement:
--   The Hermitian Lattices Theory construction uses the maj Dual unimod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/MajDual.lean#L190-L265
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/MajDual.lean#L190-L265

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementMaj
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MajLattice
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MajDual
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open scoped nonZeroDivisors
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (RingOfIntegers K) V] [IsScalarTower (RingOfIntegers K) K V]

theorem Formalism.HermitianLatticesTheory.majDual_unimod (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (RingOfIntegers K) V)
    (hU : IsUnimodular h L) (y : V) :
    y ∈ dualI h L (invDiff K) ↔ y ∈ idealSmul (invDiffSub K) L := by sorry
