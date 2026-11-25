-- Prove2me | Theorems.Thm_Formalism_HermitianLatticesTheory_majDual_realize_qsmul
-- name    : Formalism.HermitianLatticesTheory.majDual_realize_qsmul
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:41:51.682471+00:00
-- url     : https://prove2.me/theorems/ec6d3b37-9b5e-56b5-bfb6-372c213d0e09
-- title:
--   Hermitian Lattices Theory: maj Dual realize qsmul
-- statement:
--   The Hermitian Lattices Theory construction uses the maj Dual realize qsmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/MajDual.lean#L277-L291
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/MajDual.lean#L277-L291

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
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Fintype ι] [DecidableEq ι]

theorem Formalism.HermitianLatticesTheory.majDual_realize_qsmul (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (q : ℚ) (x : V) : realize b X (algebraMap ℚ K q • x) = (q : ℝ) • realize b X x := by sorry
