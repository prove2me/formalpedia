-- Prove2me | Theorems.Thm_Formalism_HermitianLatticesTheory_exampleZ_odd
-- name    : Formalism.HermitianLatticesTheory.exampleZ_odd
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:03:59.0208+00:00
-- url     : https://prove2.me/theorems/ae326f4f-2b7b-4af7-a760-b0b5d1cd6e30
-- title:
--   Hermitian Lattices Theory: example Z odd
-- statement:
--   The Hermitian Lattices Theory construction uses the example Z odd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/ExampleZ.lean#L33-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/ExampleZ.lean#L33-L35

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_ExampleZ
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLatticesTheory

theorem Formalism.HermitianLatticesTheory.exampleZ_odd {s : ℤ} (hs : s ∉ Ideal.span {(2 : ℤ)}) : Odd s := by sorry
