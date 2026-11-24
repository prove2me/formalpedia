-- Prove2me | Theorems.Thm_Formalism_HermitianLatticesTheory_traceReal_trace_smul
-- name    : Formalism.HermitianLatticesTheory.traceReal_trace_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:05:34.437618+00:00
-- url     : https://prove2.me/theorems/2b2ec2aa-f6b0-420c-9f81-662d72a6a387
-- title:
--   Hermitian Lattices Theory: trace Real trace smul
-- statement:
--   The Hermitian Lattices Theory construction uses the trace Real trace smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/TraceReal.lean#L24-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/TraceReal.lean#L24-L26

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_DefsCS
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_ThetaSummable
import Definitions.Def_Lemmata_GeneralBFactSecondSide_Imports
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_TraceReal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]

theorem Formalism.HermitianLatticesTheory.traceReal_trace_smul (q : ℚ) (z : K) :
    Algebra.trace ℚ K (algebraMap ℚ K q * z) = q * Algebra.trace ℚ K z := by sorry
