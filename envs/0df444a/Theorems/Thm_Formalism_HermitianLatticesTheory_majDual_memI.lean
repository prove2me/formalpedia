-- Prove2me | Theorems.Thm_Formalism_HermitianLatticesTheory_majDual_memI
-- name    : Formalism.HermitianLatticesTheory.majDual_memI
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:42:23.218659+00:00
-- url     : https://prove2.me/theorems/555af560-5027-48f8-b227-e324fadeeea2
-- title:
--   Hermitian Lattices Theory: maj Dual mem I
-- statement:
--   The Hermitian Lattices Theory construction uses the maj Dual mem I property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/MajDual.lean#L156-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/MajDual.lean#L156-L176

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

theorem Formalism.HermitianLatticesTheory.majDual_memI (a : K) : a ∈ majDualI K ↔ a ∈ invDiff K := by sorry
