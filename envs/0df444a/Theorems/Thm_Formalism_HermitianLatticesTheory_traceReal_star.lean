-- Prove2me | Theorems.Thm_Formalism_HermitianLatticesTheory_traceReal_star
-- name    : Formalism.HermitianLatticesTheory.traceReal_star
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:05:32.119296+00:00
-- url     : https://prove2.me/theorems/c147da8e-15f7-4845-8d62-e2dc8000f1de
-- title:
--   Hermitian Lattices Theory: trace Real star
-- statement:
--   The Hermitian Lattices Theory construction uses the trace Real star property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/TraceReal.lean#L16-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/TraceReal.lean#L16-L19

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

theorem Formalism.HermitianLatticesTheory.traceReal_star (z : K) : Algebra.trace ℚ K (starRingEnd K z) = Algebra.trace ℚ K z := by sorry
