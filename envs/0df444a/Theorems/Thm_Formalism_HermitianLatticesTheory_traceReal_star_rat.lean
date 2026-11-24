-- Prove2me | Theorems.Thm_Formalism_HermitianLatticesTheory_traceReal_star_rat
-- name    : Formalism.HermitianLatticesTheory.traceReal_star_rat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:05:29.891217+00:00
-- url     : https://prove2.me/theorems/55e757bd-8e07-4e85-8e98-16c877c3a140
-- title:
--   Hermitian Lattices Theory: trace Real star rat
-- statement:
--   The Hermitian Lattices Theory construction uses the trace Real star rat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/TraceReal.lean#L21-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/TraceReal.lean#L21-L22

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

theorem Formalism.HermitianLatticesTheory.traceReal_star_rat (q : ℚ) : starRingEnd K (algebraMap ℚ K q) = algebraMap ℚ K q := by sorry
