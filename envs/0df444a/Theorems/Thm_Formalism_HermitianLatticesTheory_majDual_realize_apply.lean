-- Prove2me | Theorems.Thm_Formalism_HermitianLatticesTheory_majDual_realize_apply
-- name    : Formalism.HermitianLatticesTheory.majDual_realize_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:42:19.313559+00:00
-- url     : https://prove2.me/theorems/90dd29cf-2181-4f68-8cb1-b32ab0d6080a
-- title:
--   Hermitian Lattices Theory: maj Dual realize apply
-- statement:
--   The Hermitian Lattices Theory construction uses the maj Dual realize apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/MajDual.lean#L62-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/MajDual.lean#L62-L65

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

theorem Formalism.HermitianLatticesTheory.majDual_realize_apply (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (x : V)
    (p : InfinitePlace K × ι × Fin 2) :
    realize b X x p = if p.2.2 = 0 then (fcoord b X p.1 x p.2.1).re
      else (fcoord b X p.1 x p.2.1).im := by sorry
