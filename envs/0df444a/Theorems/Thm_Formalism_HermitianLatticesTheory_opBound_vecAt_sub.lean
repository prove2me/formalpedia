-- Prove2me | Theorems.Thm_Formalism_HermitianLatticesTheory_opBound_vecAt_sub
-- name    : Formalism.HermitianLatticesTheory.opBound_vecAt_sub
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:05:20.929914+00:00
-- url     : https://prove2.me/theorems/95edb9ab-d329-4eb5-8db5-ed98f7d63e39
-- title:
--   Hermitian Lattices Theory: op Bound vec At sub
-- statement:
--   The Hermitian Lattices Theory construction uses the op Bound vec At sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/OpBound.lean#L33-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/OpBound.lean#L33-L35

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementMaj
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_OpBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
variable {K V ι : Type*} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Fintype ι] [DecidableEq ι]

theorem Formalism.HermitianLatticesTheory.opBound_vecAt_sub (b : Module.Basis ι K V) (v : InfinitePlace K) (x y : V) :
    vecAt b v (x - y) = vecAt b v x - vecAt b v y := by sorry
