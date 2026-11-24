-- Prove2me | Theorems.Thm_Formalism_HermitianLatticesTheory_exampleZ_not_mem_of_odd
-- name    : Formalism.HermitianLatticesTheory.exampleZ_not_mem_of_odd
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:03:55.093069+00:00
-- url     : https://prove2.me/theorems/a38a9b7d-7546-4436-9acf-2479f953596f
-- title:
--   Hermitian Lattices Theory: example Z not mem of odd
-- statement:
--   The Hermitian Lattices Theory construction uses the example Z not mem of odd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/ExampleZ.lean#L37-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/ExampleZ.lean#L37-L39

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

theorem Formalism.HermitianLatticesTheory.exampleZ_not_mem_of_odd {s : ℤ} (hs : Odd s) : s ∉ Ideal.span {(2 : ℤ)} := by sorry
