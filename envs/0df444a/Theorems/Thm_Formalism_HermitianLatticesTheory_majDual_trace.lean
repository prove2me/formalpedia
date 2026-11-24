-- Prove2me | Theorems.Thm_Formalism_HermitianLatticesTheory_majDual_trace
-- name    : Formalism.HermitianLatticesTheory.majDual_trace
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:04:57.036289+00:00
-- url     : https://prove2.me/theorems/30b2dda5-a2ed-43e6-8ba7-5a552a4cf241
-- title:
--   Hermitian Lattices Theory: maj Dual trace
-- statement:
--   The Hermitian Lattices Theory construction uses the maj Dual trace property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/MajDual.lean#L12-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/MajDual.lean#L12-L35

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

theorem Formalism.HermitianLatticesTheory.majDual_trace {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] (a : K) :
    ((Algebra.trace ℚ K a : ℚ) : ℝ) = 2 * ∑ v : InfinitePlace K, (v.embedding a).re := by sorry
